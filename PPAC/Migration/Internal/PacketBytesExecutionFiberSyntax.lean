import PPAC.Migration.Internal.PacketBytesExecutionInduction

/-! The actual unique-output fiber has the independent byte-list and natural-tail domain. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionFiberSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketBytesTraceSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def uniqueAt {m} (w n t a : Fin m) : Formula m := .all
  ((bytes w.castSucc n.castSucc t.castSucc (Fin.last m)).imp (.equal (Fin.last m) a.castSucc))

def fiberBody {m} (w n t : Fin m) : Formula (m+1) :=
  ((Formula.mem (Fin.last m) w.castSucc).conj (bytes w.castSucc n.castSucc t.castSucc (Fin.last m))).conj
    (uniqueAt w.castSucc n.castSucc t.castSucc (Fin.last m))

def fiber {m} (w n t : Fin m) : Formula m := .ex (fiberBody w n t)

def lawBody {m} (w : Fin m) : Formula (m+2) :=
  (fiber (old 2 w) (slot 2 0) (slot 2 1)).iff ((byteList (old 2 w) (slot 2 0)).conj (.mem (slot 2 1) (old 2 w)))

def allLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 2 (lawBody w)

theorem uniqueAt_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (uniqueAt w n t a).rename ρ = uniqueAt (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [uniqueAt,Formula.rename,bytes_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n t : Fin m) (ρ : Fin m → Fin k) :
    (fiber w n t).rename ρ = fiber (ρ w) (ρ n) (ρ t) := by
  simp only [fiber,fiberBody,Formula.rename,bytes_rename,uniqueAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem lawBody_lift {m k} (w : Fin m) (ρ : Fin m → Fin k) : (lawBody w).rename (lift 2 ρ) = lawBody (ρ w) := by
  simp only [lawBody,Formula.iff,Formula.rename,fiber_rename,byteList_rename,lift_old,lift_slot]

theorem allLaw_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

theorem intro_fiber {m} {Γ : Context m} (w n t a : Fin m) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (bytes w n t a))
    (hu : Derives Γ (uniqueAt w n t a)) : Derives Γ (fiber w n t) := by
  apply Derives.exI a
  exact of_eq (by simp only [fiberBody,Formula.instantiate,Formula.rename,bytes_rename,uniqueAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjI ha hb) hu)

theorem uniqueAt_at {m} {Γ : Context m} (w n t a b : Fin m) (hu : Derives Γ (uniqueAt w n t a)) (hb : Derives Γ (bytes w n t b)) : Derives Γ (.equal b a) := by
  have he : Derives Γ ((bytes w n t b).imp (.equal b a)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,bytes_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE b hu)
  exact .impE he hb

end PPAC.Migration.Internal.PacketBytesExecutionFiberSyntax
