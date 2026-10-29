import FormalResearch.FourQubitEntropy.Generic
import FormalResearch.FourQubitEntropy.SparsePoly

/-!
# Generic expressions commute with operation-preserving maps

If `f : α → β` preserves the `RingOps` operations, then each expression of `Generic.lean`
evaluated at `f ∘ z`, `f ∘ w` is `f` of the expression evaluated at `z`, `w`. With
`f = evSP v` this carries the polynomial identity of `Identity.lean` to every complex `z`, `w`.
-/

open scoped FormalResearch.FourQubitEntropy.GenericOps

namespace FormalResearch.FourQubitEntropy

/-- Apply `f` to every amplitude. -/
def State.map {α β : Type} (f : α → β) (z : State α) : State β := fun a b c d => f (z a b c d)

section Transfer

variable {α β : Type} [RingOps α] [RingOps β] {f : α → β}

theorem OpsHom.add' (hf : OpsHom f) (a b : α) : f (a + b) = f a + f b := hf.map_add a b
theorem OpsHom.mul' (hf : OpsHom f) (a b : α) : f (a * b) = f a * f b := hf.map_mul a b
theorem OpsHom.sub' (hf : OpsHom f) (a b : α) : f (a - b) = f a - f b := by
  show f (RingOps.add a (RingOps.neg b)) = RingOps.add (f a) (RingOps.neg (f b))
  rw [hf.map_add, hf.map_neg]
theorem OpsHom.lit' (hf : OpsHom f) (k : ℤ) : f (lit k : α) = (lit k : β) := hf.map_ofInt k

theorem OpsHom.sum2 (hf : OpsHom f) (g : Fin 2 → α) :
    f (sum2 g) = sum2 (fun i => f (g i)) := by
  simp [FormalResearch.FourQubitEntropy.sum2, hf.add']

theorem OpsHom.sum4 (hf : OpsHom f) (g : Fin 2 → Fin 2 → Fin 2 → Fin 2 → α) :
    f (sum4 g) = sum4 (fun a b c d => f (g a b c d)) := by
  simp [FormalResearch.FourQubitEntropy.sum4, hf.sum2]

variable (hf : OpsHom f) (z w : State α)
include hf

theorem OpsHom.normG : f (normG z w) = normG (z.map f) (w.map f) := by
  simp [FormalResearch.FourQubitEntropy.normG, hf.sum4, hf.mul', State.map]

theorem OpsHom.tr2 (M : Mat2 α) :
    f (tr2 M) = tr2 (fun a b a' b' => f (M a b a' b')) := by
  simp [FormalResearch.FourQubitEntropy.tr2, hf.sum2, hf.mul']

theorem OpsHom.tr3 (M : Mat2 α) :
    f (tr3 M) = tr3 (fun a b a' b' => f (M a b a' b')) := by
  simp [FormalResearch.FourQubitEntropy.tr3, hf.sum2, hf.mul']

theorem OpsHom.marg12 (a b a' b' : Fin 2) :
    f (marg12 z w a b a' b') = marg12 (z.map f) (w.map f) a b a' b' := by
  simp [FormalResearch.FourQubitEntropy.marg12, hf.sum2, hf.mul', State.map]
theorem OpsHom.marg13 (a b a' b' : Fin 2) :
    f (marg13 z w a b a' b') = marg13 (z.map f) (w.map f) a b a' b' := by
  simp [FormalResearch.FourQubitEntropy.marg13, hf.sum2, hf.mul', State.map]
theorem OpsHom.marg14 (a b a' b' : Fin 2) :
    f (marg14 z w a b a' b') = marg14 (z.map f) (w.map f) a b a' b' := by
  simp [FormalResearch.FourQubitEntropy.marg14, hf.sum2, hf.mul', State.map]

theorem OpsHom.Fgen : f (Fgen z w) = Fgen (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.Fgen, hf.add', hf.sub', hf.mul', hf.lit', hf.normG,
    hf.tr2, hf.tr3, hf.marg12, hf.marg13, hf.marg14]

theorem OpsHom.siteSwap (i : Fin 4) : (siteSwap i z).map f = siteSwap i (z.map f) := by
  fin_cases i <;> rfl

theorem OpsHom.rho0 (a a' : Fin 2) : f (rho0 z w a a') = rho0 (z.map f) (w.map f) a a' := by
  simp [FormalResearch.FourQubitEntropy.rho0, hf.sum2, hf.mul', State.map]

theorem OpsHom.trRho2 : f (trRho2 z w) = trRho2 (z.map f) (w.map f) := by
  simp [FormalResearch.FourQubitEntropy.trRho2, hf.sum2, hf.mul', hf.rho0]

theorem OpsHom.W1gen : f (W1gen z w) = W1gen (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.W1gen, hf.add', hf.sub', hf.mul', hf.lit',
    hf.normG, hf.trRho2, ← hf.siteSwap]

theorem OpsHom.epsSum (g : Fin 2 → Fin 2 → α) :
    f (epsSum g) = epsSum (fun a t => f (g a t)) := by
  simp [FormalResearch.FourQubitEntropy.epsSum, hf.sub']

theorem OpsHom.ztil (t0 t1 t2 t3 : Fin 2) :
    f (ztil w t0 t1 t2 t3) = ztil (w.map f) t0 t1 t2 t3 := by
  simp [FormalResearch.FourQubitEntropy.ztil, hf.mul', hf.lit', State.map]

theorem OpsHom.resRaw (L : Bool) (x0 y0 t0 o1 o2 o3 : Fin 2) :
    f (resRaw L z w x0 y0 t0 o1 o2 o3) = resRaw L (z.map f) (w.map f) x0 y0 t0 o1 o2 o3 := by
  cases L <;>
  simp [FormalResearch.FourQubitEntropy.resRaw, hf.add', hf.mul', hf.epsSum, hf.ztil, State.map,
    hf.map_zero, hf.lit']

theorem OpsHom.resSym (L : Bool) (x y t o1 o2 o3 : Fin 2) :
    f (resSym L z w x y t o1 o2 o3) = resSym L (z.map f) (w.map f) x y t o1 o2 o3 := by
  simp [FormalResearch.FourQubitEntropy.resSym, hf.add', hf.resRaw]

theorem OpsHom.resTensor (x y t o1 o2 o3 : Fin 2) :
    f (resTensor z w x y t o1 o2 o3) = resTensor (z.map f) (w.map f) x y t o1 o2 o3 := by
  simp [FormalResearch.FourQubitEntropy.resTensor, hf.sub', hf.mul', hf.lit', hf.resSym]

theorem OpsHom.resSlot (x y t : Fin 2) :
    f (resSlot z w x y t) = resSlot (z.map f) (w.map f) x y t := by
  simp [FormalResearch.FourQubitEntropy.resSlot, hf.sum2, hf.mul', hf.resTensor]

theorem OpsHom.resNorm0 : f (resNorm0 z w) = resNorm0 (z.map f) (w.map f) := by
  simp [FormalResearch.FourQubitEntropy.resNorm0, hf.add', hf.mul', hf.lit', hf.resSlot]

theorem OpsHom.actSite (s : Fin 4) (a b c d : Fin 2) :
    f (actSite s z w a b c d) = actSite s (z.map f) (w.map f) a b c d := by
  fin_cases s <;>
  simp [FormalResearch.FourQubitEntropy.actSite, hf.sum2, hf.mul', hf.rho0, ← hf.siteSwap,
    State.map]

theorem OpsHom.pairVec (i j : Fin 4) (a b c d : Fin 2) :
    f (pairVec i j z w a b c d) = pairVec i j (z.map f) (w.map f) a b c d := by
  simp [FormalResearch.FourQubitEntropy.pairVec, hf.sub', hf.actSite]

theorem OpsHom.pairNorm (i j : Fin 4) :
    f (pairNorm i j z w) = pairNorm i j (z.map f) (w.map f) := by
  simp [FormalResearch.FourQubitEntropy.pairNorm, hf.sum4, hf.mul', hf.pairVec]

theorem OpsHom.pairSum : f (pairSum z w) = pairSum (z.map f) (w.map f) := by
  simp [FormalResearch.FourQubitEntropy.pairSum, hf.add', hf.pairNorm]

theorem OpsHom.sexticDefect : f (sexticDefect z w) = sexticDefect (z.map f) (w.map f) := by
  simp only [FormalResearch.FourQubitEntropy.sexticDefect, FormalResearch.FourQubitEntropy.defectG,
    hf.add', hf.sub', hf.mul', hf.lit', hf.Fgen, hf.normG, hf.W1gen, hf.resNorm0, hf.pairSum,
    ← hf.siteSwap]

end Transfer

end FormalResearch.FourQubitEntropy
