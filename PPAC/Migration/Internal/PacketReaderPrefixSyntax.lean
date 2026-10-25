import PPAC.Migration.Internal.PacketReaderVarintSegmentSyntax
import PPAC.Migration.Internal.PacketByteInputLaws

/-! A fixed Formula5 for successful bounded-byte prefix extraction. The independent canonical segment, actual splice, strict suffix-code descent and every return candidate remain object quantified. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open PacketReaderVarintSegmentSyntax (guard guard_rename)
open SyntaxRenameQuerySyntax (of_eq)

def five {m} (a b c d e : Fin m) : Fin 5 → Fin m :=
  Fin.cases a (Fin.cases b (Fin.cases c (Fin.cases d (Fin.cases e Fin.elim0))))

def resultBody {m} (w B z o L v s A p : Fin m) : Formula (m+5) :=
  (PacketVarintSyntax.canonical (old 5 w) (slot 5 0) (slot 5 1)).conj
  ((StructuralListSpliceSyntax.splice (old 5 w) (slot 5 1) (slot 5 2) (old 5 L)).conj
  ((PacketByteInputSyntax.byteList (old 5 w) (slot 5 2)).conj
  ((Formula.mem (slot 5 2) (old 5 L)).conj
  ((guard (old 5 o) (slot 5 0) (old 5 s)).conj
  ((PacketAffineSyntax.equation (old 5 w) (slot 5 0) (old 5 v) (old 5 s) (slot 5 3)).conj
  ((StructuralListSyntax.consCode (old 5 w) (slot 5 3) (old 5 A) (slot 5 4)).conj
    (PacketReaderEvalSyntax.eval (old 5 w) (old 5 B) (old 5 z) (old 5 o)
      (slot 5 2) (old 5 z) (old 5 o) (slot 5 4) (old 5 p))))))))

def result {m} (w B z o L v s A p : Fin m) : Formula m :=
  existsMany 5 (resultBody w B z o L v s A p)

def caseFormula {m} (w B z o L v s A O p : Fin m) : Formula m :=
  (PacketByteInputSyntax.byteList w L).imp
  ((PacketReaderStepSyntax.state w L v s A).imp
  ((empty s).neg.imp
  ((StructuralListSyntax.nilCode w L).neg.imp
  ((PacketReaderEvalSyntax.eval w B z o L v s A p).imp
  ((PacketReaderReturnSyntax.some w O p).imp (result w B z o L v s A p))))))

def body {m} (w B z o L : Fin m) : Formula (m+5) :=
  caseFormula (old 5 w) (old 5 B) (old 5 z) (old 5 o) (old 5 L)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)

def property {m} (w B z o L : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 5 (body w B z o L)

def earlier {m} (w B z o L : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) L.castSucc).imp
    (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m))))

def allProperties {m} (w B z o : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp
    (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)))

def matrix : Formula 5 := property 0 1 2 3 4

theorem resultBody_lift {m k} (w B z o L v s A p : Fin m) (ρ : Fin m → Fin k) :
    (resultBody w B z o L v s A p).rename (lift 5 ρ) =
      resultBody (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ A) (ρ p) := by
  simp only [resultBody,Formula.rename,PacketVarintSyntax.canonical_rename,
    StructuralListSpliceSyntax.splice_rename,PacketByteInputSyntax.byteList_rename,
    guard_rename,PacketAffineSyntax.equation_rename,StructuralListSyntax.consCode_rename,
    PacketReaderEvalSyntax.eval_rename,lift_old,lift_slot]

theorem result_rename {m k} (w B z o L v s A p : Fin m) (ρ : Fin m → Fin k) :
    (result w B z o L v s A p).rename ρ =
      result (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ A) (ρ p) := by
  simp only [result,existsMany_rename,resultBody_lift]

theorem caseFormula_rename {m k} (w B z o L v s A O p : Fin m) (ρ : Fin m → Fin k) :
    (caseFormula w B z o L v s A O p).rename ρ =
      caseFormula (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ v) (ρ s) (ρ A) (ρ O) (ρ p) := by
  simp only [caseFormula,Formula.rename,Formula.neg,PacketByteInputSyntax.byteList_rename,
    PacketReaderStepSyntax.state_rename,empty_rename,StructuralListSyntax.nilCode_rename,
    PacketReaderEvalSyntax.eval_rename,PacketReaderReturnSyntax.some_rename,result_rename]

theorem body_lift {m k} (w B z o L : Fin m) (ρ : Fin m → Fin k) :
    (body w B z o L).rename (lift 5 ρ) = body (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) := by
  simp only [body,caseFormula_rename,lift_old,lift_slot]

theorem property_rename {m k} (w B z o L : Fin m) (ρ : Fin m → Fin k) :
    (property w B z o L).rename ρ = property (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) := by
  simp only [property,OriginalUniversalBlock.allMany_rename,body_lift]

theorem earlier_rename {m k} (w B z o L : Fin m) (ρ : Fin m → Fin k) :
    (earlier w B z o L).rename ρ = earlier (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem allProperties_rename {m k} (w B z o : Fin m) (ρ : Fin m → Fin k) :
    (allProperties w B z o).rename ρ = allProperties (ρ w) (ρ B) (ρ z) (ρ o) := by
  simp only [allProperties,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 4 → Fin m) (L : Fin m) :
    MinimalPredicates.pred matrix ρ L = property (ρ 0) (ρ 1) (ρ 2) (ρ 3) L := by
  have h0 : Fin.lastCases L ρ (0 : Fin 5) = ρ 0 := by change Fin.lastCases L ρ (0 : Fin 4).castSucc = ρ 0; exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases L ρ (1 : Fin 5) = ρ 1 := by change Fin.lastCases L ρ (1 : Fin 4).castSucc = ρ 1; exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases L ρ (2 : Fin 5) = ρ 2 := by change Fin.lastCases L ρ (2 : Fin 4).castSucc = ρ 2; exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases L ρ (3 : Fin 5) = ρ 3 := by change Fin.lastCases L ρ (3 : Fin 4).castSucc = ρ 3; exact Fin.lastCases_castSucc _
  have h4 : Fin.lastCases L ρ (4 : Fin 5) = L := by change Fin.lastCases L ρ (Fin.last 4) = L; exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1,h2,h3,h4]

theorem intro_result {m} {Γ : Context m} (w B z o L v s A p n C T u c : Fin m)
    (hCanonical : Derives Γ (PacketVarintSyntax.canonical w n C))
    (hSplice : Derives Γ (StructuralListSpliceSyntax.splice w C T L))
    (hBytes : Derives Γ (PacketByteInputSyntax.byteList w T)) (hBelow : Derives Γ (.mem T L))
    (hGuard : Derives Γ (guard o n s)) (hEquation : Derives Γ (PacketAffineSyntax.equation w n v s u))
    (hCons : Derives Γ (StructuralListSyntax.consCode w u A c))
    (hEval : Derives Γ (PacketReaderEvalSyntax.eval w B z o T z o c p)) :
    Derives Γ (result w B z o L v s A p) := by
  apply HornBinderRules.intro_many 5 _ (five n C T u c)
  exact of_eq (by
    simp only [resultBody,Formula.rename,PacketVarintSyntax.canonical_rename,
      StructuralListSpliceSyntax.splice_rename,PacketByteInputSyntax.byteList_rename,
      guard_rename,PacketAffineSyntax.equation_rename,StructuralListSyntax.consCode_rename,
      PacketReaderEvalSyntax.eval_rename,assign_old,assign_slot,five]; rfl)
    (.conjI hCanonical (.conjI hSplice (.conjI hBytes (.conjI hBelow
      (.conjI hGuard (.conjI hEquation (.conjI hCons hEval)))))))

theorem at_fields {m} {Γ : Context m} (w B z o L v s A O p : Fin m)
    (hp : Derives Γ (property w B z o L)) : Derives Γ (caseFormula w B z o L v s A O p) := by
  exact of_eq (by simp only [body,caseFormula_rename,assign_old,assign_slot,five]; rfl)
    (OriginalUniversalBlock.at_many 5 (body w B z o L) (five v s A O p) hp)

theorem earlier_at {m} {Γ : Context m} (w B z o L X : Fin m)
    (hi : Derives Γ (earlier w B z o L)) (hX : Derives Γ (.mem X w))
    (hBelow : Derives Γ (.mem X L)) : Derives Γ (property w B z o X) := by
  have h : Derives Γ ((Formula.mem X w).imp ((Formula.mem X L).imp (property w B z o X))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE X hi)
  exact .impE (.impE h hX) hBelow

end PPAC.Migration.Internal.PacketReaderPrefixSyntax
