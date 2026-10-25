import PPAC.Migration.Internal.StructuralReverseFieldGraph

/-! Actual original list codes, shared internal length, and the full reverse-field equivalence define reversal. -/
namespace PPAC.Migration.Internal.StructuralListReverseSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open StructuralListFieldSyntax (field field_rename)
open StructuralReverseFieldSyntax (value value_rename)
open SyntaxRenameQuerySyntax (of_eq)

def reading {m} (w n l r : Fin m) : Formula m := .all (.all
  ((Formula.mem (Fin.last m).castSucc l.castSucc.castSucc).imp
    ((field w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      (value w.castSucc.castSucc n.castSucc.castSucc l.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def atLength {m} (w n l r : Fin m) : Formula m :=
  (hasLength w n l).conj ((hasLength w r l).conj (reading w n l r))

def reverses {m} (w n r : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (atLength w.castSucc n.castSucc (Fin.last m) r.castSucc))

def existsReverse {m} (w n : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (reverses w.castSucc n.castSucc (Fin.last m)))

def fiber {m} (w n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (reverses w.castSucc n.castSucc (Fin.last m))).conj (.all
    ((reverses w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem reading_rename {m k} (w n l r : Fin m) (ρ : Fin m → Fin k) :
    (reading w n l r).rename ρ = reading (ρ w) (ρ n) (ρ l) (ρ r) := by
  simp only [reading,Formula.rename,Formula.iff,field_rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem atLength_rename {m k} (w n l r : Fin m) (ρ : Fin m → Fin k) :
    (atLength w n l r).rename ρ = atLength (ρ w) (ρ n) (ρ l) (ρ r) := by
  simp only [atLength,Formula.rename,hasLength_rename,reading_rename]

theorem reverses_rename {m k} (w n r : Fin m) (ρ : Fin m → Fin k) :
    (reverses w n r).rename ρ = reverses (ρ w) (ρ n) (ρ r) := by
  simp only [reverses,Formula.rename,atLength_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem existsReverse_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (existsReverse w n).rename ρ = existsReverse (ρ w) (ρ n) := by
  simp only [existsReverse,Formula.rename,reverses_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w n).rename ρ = fiber (ρ w) (ρ n) := by
  simp only [fiber,Formula.rename,reverses_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem reading_at {m} {Γ : Context m} (w n l r i y : Fin m) (hr : Derives Γ (reading w n l r))
    (hi : Derives Γ (.mem i l)) : Derives Γ ((field w r i y).iff (value w n l i y)) := by
  have hp : Derives Γ ((Formula.mem i l).imp ((field w r i y).iff (value w n l i y))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,Formula.iff,field_rename,value_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE y (Derives.allE i hr))
  exact .impE hp hi

theorem intro_reverse {m} {Γ : Context m} (w n l r : Fin m) (hl : Derives Γ (.mem l w))
    (hr : Derives Γ (atLength w n l r)) : Derives Γ (reverses w n r) := by
  apply Derives.exI l
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,atLength_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hl hr)

theorem intro_exists {m} {Γ : Context m} (w n r : Fin m) (hr : Derives Γ (.mem r w))
    (hh : Derives Γ (reverses w n r)) : Derives Γ (existsReverse w n) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,reverses_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hr hh)

theorem length_subst {m} {Γ : Context m} (w n l k r : Fin m) (he : Derives Γ (.equal l k))
    (hh : Derives Γ (atLength w n l r)) : Derives Γ (atLength w n k r) := by
  let P := atLength w.castSucc n.castSucc (Fin.last m) r.castSucc
  have h0 : P.instantiate l = atLength w n l r := by simp only [P,Formula.instantiate,atLength_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate k = atLength w n k r := by simp only [P,Formula.instantiate,atLength_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

end PPAC.Migration.Internal.StructuralListReverseSyntax
