import Mathlib
import QVCheckImpl.Impl3

theorem native_psi : QVCheck.checkPsi () = true := by native_decide
theorem native_inv : QVCheck.checkInvariant () = true := by native_decide
theorem native_struct : QVCheck.checkStructure () = true := by native_decide
#print axioms native_struct
