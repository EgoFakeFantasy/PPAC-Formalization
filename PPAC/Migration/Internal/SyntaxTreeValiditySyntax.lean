import PPAC.Migration.Internal.ObjectSyntaxTypedFields

/-! 原有限输入的树有效性合取与对象等词传输，不使用宿主良基性。 -/
namespace PPAC.Migration.Internal.SyntaxTreeValiditySyntax
open Source SourceAlgebra SourceLogic StructuralTreeValiditySyntax

def validInputs {m} : (k : Nat) → Fin m → (Fin k → Fin m) → Formula m
  | 0, w, _ => .equal w w
  | k+1, w, xs => (valid w (xs 0)).conj (validInputs k w (fun j => xs j.succ))

theorem validInputs_rename {m n} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (r : Fin m → Fin n) :
    (validInputs k w xs).rename r = validInputs k (r w) (fun j => r (xs j)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [validInputs, Formula.rename, valid_rename, ih]

theorem inputs_at {m} {Γ : Context m} (k : Nat) (w : Fin m) (xs : Fin k → Fin m) (j : Fin k)
    (hh : Derives Γ (validInputs k w xs)) : Derives Γ (valid w (xs j)) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun a => ?_) j
    · exact .conjL hh
    · exact ih (fun a => xs a.succ) a (.conjR hh)

theorem valid_subst {m} {Γ : Context m} (w n q : Fin m) (he : Derives Γ (.equal n q))
    (hv : Derives Γ (valid w n)) : Derives Γ (valid w q) := by
  have hi : Derives Γ ((valid w.castSucc (Fin.last m)).instantiate n) := by
    simpa only [Formula.instantiate, valid_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
  have ho := Derives.eqSubst (valid w.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, valid_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.SyntaxTreeValiditySyntax
