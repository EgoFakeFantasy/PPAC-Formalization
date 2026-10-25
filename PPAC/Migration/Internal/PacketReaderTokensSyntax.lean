import PPAC.Migration.Internal.PacketTokensBytes
import PPAC.Migration.Internal.PacketReaderOutputCons
import PPAC.Migration.Internal.PacketReaderTokenUnits

/-! One fixed Formula5 quantifies every actual byte input, accumulator, final ordered output and return candidate. -/
namespace PPAC.Migration.Internal.PacketReaderTokensSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def agreement {m} (w B z o bytes A O p : Fin m) : Formula m :=
  (PacketReaderEvalSyntax.eval w B z o bytes z o A p).iff (PacketReaderReturnSyntax.some w O p)

def caseFormula {m} (w B z o n bytes A O p : Fin m) : Formula m :=
  (StructuralListTraceSyntax.valid w A).imp ((PacketTokensBytes.encoded w n bytes).imp
    ((PacketReaderOutputOrder.output w A n O).imp (agreement w B z o bytes A O p)))

def body {m} (w B z o n : Fin m) : Formula (m+4) :=
  caseFormula (old 4 w) (old 4 B) (old 4 z) (old 4 o) (old 4 n) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)

def property {m} (w B z o n : Fin m) : Formula m :=
  (StructuralListTraceSyntax.valid w n).imp (OriginalUniversalBlock.allMany 4 (body w B z o n))

def earlier {m} (w B z o n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m))))

def allProperties {m} (w B z o : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)))

def matrix : Formula 5 := property 0 1 2 3 4

theorem agreement_rename {m k} (w B z o bytes A O p : Fin m) (ρ : Fin m → Fin k) :
    (agreement w B z o bytes A O p).rename ρ = agreement (ρ w) (ρ B) (ρ z) (ρ o) (ρ bytes) (ρ A) (ρ O) (ρ p) := by
  simp only [agreement,Formula.iff,Formula.rename,PacketReaderEvalSyntax.eval_rename,PacketReaderReturnSyntax.some_rename]

theorem caseFormula_rename {m k} (w B z o n bytes A O p : Fin m) (ρ : Fin m → Fin k) :
    (caseFormula w B z o n bytes A O p).rename ρ = caseFormula (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) (ρ bytes) (ρ A) (ρ O) (ρ p) := by
  simp only [caseFormula,Formula.rename,StructuralListTraceSyntax.valid_rename,PacketTokensBytes.encoded_rename,PacketReaderOutputOrder.output_rename,agreement_rename]

theorem body_lift {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (body w B z o n).rename (lift 4 ρ) = body (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [body,caseFormula_rename,lift_old,lift_slot]

theorem property_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (property w B z o n).rename ρ = property (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [property,Formula.rename,StructuralListTraceSyntax.valid_rename,OriginalUniversalBlock.allMany_rename,body_lift]

theorem earlier_rename {m k} (w B z o n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w B z o n).rename ρ = earlier (ρ w) (ρ B) (ρ z) (ρ o) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem allProperties_rename {m k} (w B z o : Fin m) (ρ : Fin m → Fin k) :
    (allProperties w B z o).rename ρ = allProperties (ρ w) (ρ B) (ρ z) (ρ o) := by
  simp only [allProperties,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 4 → Fin m) (n : Fin m) :
    MinimalPredicates.pred matrix ρ n = property (ρ 0) (ρ 1) (ρ 2) (ρ 3) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 5) = ρ 0 := by change Fin.lastCases n ρ (0 : Fin 4).castSucc = ρ 0; exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 5) = ρ 1 := by change Fin.lastCases n ρ (1 : Fin 4).castSucc = ρ 1; exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases n ρ (2 : Fin 5) = ρ 2 := by change Fin.lastCases n ρ (2 : Fin 4).castSucc = ρ 2; exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases n ρ (3 : Fin 5) = ρ 3 := by change Fin.lastCases n ρ (3 : Fin 4).castSucc = ρ 3; exact Fin.lastCases_castSucc _
  have h4 : Fin.lastCases n ρ (4 : Fin 5) = n := by change Fin.lastCases n ρ (Fin.last 4) = n; exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1,h2,h3,h4]

theorem at_fields {m} {Γ : Context m} (w B z o n bytes A O p : Fin m)
    (hp : Derives Γ (property w B z o n)) (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) :
    Derives Γ (caseFormula w B z o n bytes A O p) := by
  exact of_eq (by simp only [body,caseFormula_rename,assign_old,assign_slot,PacketVarintPrefixRecursionSyntax.four]; rfl)
    (OriginalUniversalBlock.at_many 4 (body w B z o n) (PacketVarintPrefixRecursionSyntax.four bytes A O p) (.impE hp hn))

theorem earlier_at {m} {Γ : Context m} (w B z o n t : Fin m) (hi : Derives Γ (earlier w B z o n))
    (ht : Derives Γ (.mem t w)) (htn : Derives Γ (.mem t n)) : Derives Γ (property w B z o t) := by
  have h : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (property w B z o t))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE t hi)
  exact .impE (.impE h ht) htn

end PPAC.Migration.Internal.PacketReaderTokensSyntax
