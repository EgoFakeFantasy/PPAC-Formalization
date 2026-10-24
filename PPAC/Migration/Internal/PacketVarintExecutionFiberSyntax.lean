import PPAC.Migration.Internal.PacketVarintExecutionLiterals

/-! The canonical unique-list fiber includes the independent byte guard and quantifies all candidate competitors. -/
namespace PPAC.Migration.Internal.PacketVarintExecutionFiberSyntax
open Source SourceAlgebra SourceLogic PacketVarintSyntax PacketByteInputSyntax
open SyntaxRenameQuerySyntax (of_eq)

def uniqueAt {m} (w n s : Fin m) : Formula m := .all
  ((canonical w.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) s.castSucc))

def fiberBody {m} (w n : Fin m) : Formula (m+1) :=
  ((Formula.mem (Fin.last m) w.castSucc).conj (canonical w.castSucc n.castSucc (Fin.last m))).conj
    ((byteList w.castSucc (Fin.last m)).conj (uniqueAt w.castSucc n.castSucc (Fin.last m)))

def fiber {m} (w n : Fin m) : Formula m := .ex (fiberBody w n)

def allLaw {m} (w : Fin m) : Formula m := .all ((fiber w.castSucc (Fin.last m)).iff (.mem (Fin.last m) w.castSucc))

theorem uniqueAt_rename {m k} (w n s : Fin m) (ρ : Fin m → Fin k) : (uniqueAt w n s).rename ρ = uniqueAt (ρ w) (ρ n) (ρ s) := by
  simp only [uniqueAt,Formula.rename,canonical_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) : (fiber w n).rename ρ = fiber (ρ w) (ρ n) := by
  simp only [fiber,fiberBody,Formula.rename,canonical_rename,byteList_rename,uniqueAt_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem allLaw_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,Formula.iff,Formula.rename,fiber_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w n s : Fin m) (hs : Derives Γ (.mem s w)) (hc : Derives Γ (canonical w n s))
    (hb : Derives Γ (byteList w s)) (hu : Derives Γ (uniqueAt w n s)) : Derives Γ (fiber w n) := by
  apply Derives.exI s
  exact of_eq (by simp only [fiberBody,Formula.instantiate,Formula.rename,canonical_rename,byteList_rename,uniqueAt_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI (.conjI hs hc) (.conjI hb hu))

end PPAC.Migration.Internal.PacketVarintExecutionFiberSyntax
