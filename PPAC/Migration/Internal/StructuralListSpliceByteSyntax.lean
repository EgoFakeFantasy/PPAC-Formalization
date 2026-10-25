import PPAC.Migration.Internal.StructuralListSplice
import PPAC.Migration.Internal.PacketVarintExecutionHelpers

/-! A fixed Formula2 states preservation of the existing independent ByteList predicate by actual splice, with every tail and joined candidate internally quantified. -/
namespace PPAC.Migration.Internal.StructuralListSpliceByteSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def caseFormula {m} (w n t a : Fin m) : Formula m :=
  (PacketByteInputSyntax.byteList w t).imp
    ((StructuralListSpliceSyntax.splice w n t a).imp (PacketByteInputSyntax.byteList w a))

def body {m} (w n : Fin m) : Formula (m+2) :=
  caseFormula (old 2 w) (old 2 n) (slot 2 0) (slot 2 1)

def preserves {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 2 (body w n)

def property {m} (w n : Fin m) : Formula m := (PacketByteInputSyntax.byteList w n).imp (preserves w n)

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

def allProperties {m} (w : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc (Fin.last m)))

def matrix : Formula 2 := property 0 1

theorem caseFormula_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (caseFormula w n t a).rename ρ = caseFormula (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [caseFormula,Formula.rename,PacketByteInputSyntax.byteList_rename,StructuralListSpliceSyntax.splice_rename]

theorem body_lift {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (body w n).rename (lift 2 ρ) = body (ρ w) (ρ n) := by
  simp only [body,caseFormula_rename,lift_old,lift_slot]

theorem preserves_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (preserves w n).rename ρ = preserves (ρ w) (ρ n) := by
  simp only [preserves,OriginalUniversalBlock.allMany_rename,body_lift]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,Formula.rename,PacketByteInputSyntax.byteList_rename,preserves_rename]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem allProperties_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (allProperties w).rename ρ = allProperties (ρ w) := by
  simp only [allProperties,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) :
    MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0; exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by change Fin.lastCases n ρ (Fin.last 1) = n; exact Fin.lastCases_last
  simp only [MinimalPredicates.pred,matrix,property_rename,h0,h1]

theorem at_fields {m} {Γ : Context m} (w n t a : Fin m)
    (hp : Derives Γ (property w n)) (hn : Derives Γ (PacketByteInputSyntax.byteList w n)) :
    Derives Γ (caseFormula w n t a) := by
  exact of_eq (by simp only [body,caseFormula_rename,assign_old,assign_slot]; rfl)
    (OriginalUniversalBlock.at_many 2 (body w n) (SyntaxAtomSyntax.two t a) (.impE hp hn))

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (hi : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x w)) (hb : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have h : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (property w x))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE x hi)
  exact .impE (.impE h hx) hb

end PPAC.Migration.Internal.StructuralListSpliceByteSyntax
