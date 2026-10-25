import PPAC.Migration.Internal.ObjectPacketReaderVarintSegment

/-! A fixed object Formula2 states that appending a real singleton has the full original Snoc length, prefix-field and last-field contract. -/
namespace PPAC.Migration.Internal.StructuralListSpliceSnocSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def five {m} (h S r l L : Fin m) : Fin 5 → Fin m := Fin.cases h (Fin.cases S (Fin.cases r (Fin.cases l (Fin.cases L Fin.elim0))))

def caseFormula {m} (w n h S r l L : Fin m) : Formula m :=
  (Formula.mem h w).imp ((StructuralListLengthSyntax.hasLength w n l).imp
    ((PacketVarintCanonicalRecursionSyntax.singleton w h S).imp ((StructuralListSpliceSyntax.splice w n S r).imp
      ((successor L l).imp (StructuralListReverseConsContract.snoc w n l L h r)))))

def body {m} (w n : Fin m) : Formula (m+5) :=
  caseFormula (old 5 w) (old 5 n) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)

def property {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 5 (body w n)

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

def matrix : Formula 2 := property 0 1

theorem caseFormula_rename {m k} (w n h S r l L : Fin m) (ρ : Fin m → Fin k) :
    (caseFormula w n h S r l L).rename ρ = caseFormula (ρ w) (ρ n) (ρ h) (ρ S) (ρ r) (ρ l) (ρ L) := by
  simp only [caseFormula,Formula.rename,StructuralListLengthSyntax.hasLength_rename,PacketVarintCanonicalRecursionSyntax.singleton_rename,StructuralListSpliceSyntax.splice_rename,successor_rename,StructuralListReverseConsContract.snoc_rename]

theorem body_lift {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (body w n).rename (lift 5 ρ) = body (ρ w) (ρ n) := by
  simp only [body,caseFormula_rename,lift_old,lift_slot]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property,OriginalUniversalBlock.allMany_rename,body_lift]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier,Formula.rename,property_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) :
    MinimalPredicates.pred matrix ρ n = property (ρ 0) n := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0; exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by change Fin.lastCases n ρ (Fin.last 1) = n; exact Fin.lastCases_last
  simp only [matrix,MinimalPredicates.pred,property_rename,h0,h1]

theorem at_fields {m} {Γ : Context m} (w n h S r l L : Fin m) (hp : Derives Γ (property w n)) :
    Derives Γ (caseFormula w n h S r l L) :=
  of_eq (by simp only [body,caseFormula_rename,assign_old,assign_slot,five]; rfl)
    (OriginalUniversalBlock.at_many 5 (body w n) (five h S r l L) hp)

theorem earlier_at {m} {Γ : Context m} (w n t : Fin m) (hi : Derives Γ (earlier w n))
    (ht : Derives Γ (.mem t w)) (hBelow : Derives Γ (.mem t n)) : Derives Γ (property w t) := by
  have h : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (property w t))) :=
    of_eq (by simp only [Formula.instantiate,Formula.rename,property_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (Derives.allE t hi)
  exact .impE (.impE h ht) hBelow

end PPAC.Migration.Internal.StructuralListSpliceSnocSyntax
