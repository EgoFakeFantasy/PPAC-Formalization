import PPAC.Migration.Internal.PacketTokenUniqueInduction

/-! The real token execution has a typed unique output fiber on its exact internal domain. -/
namespace PPAC.Migration.Internal.PacketTokenExecutionSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

def uniqueAt {m} (w n t a : Fin m) : Formula m := .all
  ((accepted w.castSucc n.castSucc t.castSucc (Fin.last m)).imp (.equal (Fin.last m) a.castSucc))

def fiber {m} (w n t : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj ((accepted w.castSucc n.castSucc t.castSucc (Fin.last m)).conj
    (uniqueAt w.castSucc n.castSucc t.castSucc (Fin.last m))))

def lawBody {m} (w : Fin m) : Formula (m+2) :=
  (fiber (old 2 w) (slot 2 0) (slot 2 1)).iff ((Formula.mem (slot 2 0) (old 2 w)).conj (.mem (slot 2 1) (old 2 w)))

def allLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 2 (lawBody w)

theorem uniqueAt_rename {m j} (w n t a : Fin m) (ρ : Fin m → Fin j) :
    (uniqueAt w n t a).rename ρ = uniqueAt (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [uniqueAt,Formula.rename,accepted_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m j} (w n t : Fin m) (ρ : Fin m → Fin j) :
    (fiber w n t).rename ρ = fiber (ρ w) (ρ n) (ρ t) := by
  simp only [fiber,Formula.rename,accepted_rename,uniqueAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem lawBody_lift {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (lawBody w).rename (lift 2 ρ) = lawBody (ρ w) := by
  simp only [lawBody,Formula.iff,Formula.rename,fiber_rename,lift_old,lift_slot]

theorem allLaw_rename {m j} (w : Fin m) (ρ : Fin m → Fin j) :
    (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

theorem intro_fiber {m} {Γ : Context m} (w n t a : Fin m) (ha : Derives Γ (.mem a w))
    (ht : Derives Γ (accepted w n t a)) (hu : Derives Γ (uniqueAt w n t a)) : Derives Γ (fiber w n t) := by
  apply Derives.exI a
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,accepted_rename,uniqueAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
    (.conjI ha (.conjI ht hu))

theorem uniqueAt_at {m} {Γ : Context m} (w n t c a : Fin m) (hu : Derives Γ (uniqueAt w n t c))
    (ha : Derives Γ (accepted w n t a)) : Derives Γ (.equal a c) := by
  have hi : Derives Γ ((accepted w n t a).imp (.equal a c)) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,accepted_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE a hu)
  exact .impE hi ha

end PPAC.Migration.Internal.PacketTokenExecutionSyntax
