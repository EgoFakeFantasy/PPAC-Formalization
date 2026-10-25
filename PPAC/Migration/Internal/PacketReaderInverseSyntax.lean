import PPAC.Migration.Internal.PacketTokensBytes
import PPAC.Migration.Internal.PacketReaderOutputBackward
import PPAC.Migration.Internal.PacketReaderEvalSyntax
import PPAC.Migration.Internal.PacketByteInputLaws

/-! One fixed Formula5 expresses successful bounded-reader inversion with an actual internal token witness, independent encoding, exact output order and arbitrary object accumulator, payload and return candidates. -/
namespace PPAC.Migration.Internal.PacketReaderInverseSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def resultBody {m} (w L A O : Fin m) : Formula (m+1) :=
  (PacketTokensBytes.encoded w.castSucc (Fin.last m) L.castSucc).conj
    (PacketReaderOutputOrder.output w.castSucc A.castSucc (Fin.last m) O.castSucc)

def result {m} (w L A O : Fin m) : Formula m := .ex (resultBody w L A O)

def caseFormula {m} (w B z o L A O p : Fin m) : Formula m :=
  (PacketByteInputSyntax.byteList w L).imp
    ((PacketReaderEvalSyntax.eval w B z o L z o A p).imp
      ((PacketReaderReturnSyntax.some w O p).imp (result w L A O)))

def body {m} (w B z o L : Fin m) : Formula (m+3) :=
  caseFormula (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 L)
    (slot 3 0) (slot 3 1) (slot 3 2)

def property {m} (w B z o L : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 3 (body w B z o L)

def earlier {m} (w B z o L : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) L.castSucc).imp
    (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m))))

def allProperties {m} (w B z o : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp
    (property w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m)))

def matrix : Formula 5 := property 0 1 2 3 4

theorem resultBody_lift {m k} (w L A O : Fin m) (ρ : Fin m → Fin k) :
    (resultBody w L A O).rename (Formula.liftRen ρ) = resultBody (ρ w) (ρ L) (ρ A) (ρ O) := by
  simp only [resultBody,Formula.rename,PacketTokensBytes.encoded_rename,
    PacketReaderOutputOrder.output_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem result_rename {m k} (w L A O : Fin m) (ρ : Fin m → Fin k) :
    (result w L A O).rename ρ = result (ρ w) (ρ L) (ρ A) (ρ O) := by
  simp only [result,Formula.rename,resultBody_lift]

theorem caseFormula_rename {m k} (w B z o L A O p : Fin m) (ρ : Fin m → Fin k) :
    (caseFormula w B z o L A O p).rename ρ =
      caseFormula (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ A) (ρ O) (ρ p) := by
  simp only [caseFormula,Formula.rename,PacketByteInputSyntax.byteList_rename,
    PacketReaderEvalSyntax.eval_rename,PacketReaderReturnSyntax.some_rename,result_rename]

theorem body_lift {m k} (w B z o L : Fin m) (ρ : Fin m → Fin k) :
    (body w B z o L).rename (lift 3 ρ) = body (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) := by
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

theorem intro_result {m} {Γ : Context m} (w L A O tokens : Fin m)
    (hEncoded : Derives Γ (PacketTokensBytes.encoded w tokens L))
    (hOutput : Derives Γ (PacketReaderOutputOrder.output w A tokens O)) :
    Derives Γ (result w L A O) := by
  apply Derives.exI tokens
  exact of_eq (by simp only [resultBody,Formula.instantiate,Formula.rename,
    PacketTokensBytes.encoded_rename,PacketReaderOutputOrder.output_rename,
    Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hEncoded hOutput)

theorem at_fields {m} {Γ : Context m} (w B z o L A O p : Fin m)
    (hp : Derives Γ (property w B z o L)) : Derives Γ (caseFormula w B z o L A O p) := by
  exact of_eq (by simp only [body,caseFormula_rename,assign_old,assign_slot]; rfl)
    (OriginalUniversalBlock.at_many 3 (body w B z o L) (SyntaxAtomSyntax.three A O p) hp)

theorem earlier_at {m} {Γ : Context m} (w B z o L X : Fin m)
    (hi : Derives Γ (earlier w B z o L)) (hX : Derives Γ (.mem X w))
    (hBelow : Derives Γ (.mem X L)) : Derives Γ (property w B z o X) := by
  have h : Derives Γ ((Formula.mem X w).imp ((Formula.mem X L).imp (property w B z o X))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,
      Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE X hi)
  exact .impE (.impE h hX) hBelow

end PPAC.Migration.Internal.PacketReaderInverseSyntax
