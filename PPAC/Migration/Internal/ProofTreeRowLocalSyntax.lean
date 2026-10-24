import PPAC.Migration.Internal.ProofAllTableRenaming
import YesMetaZFC.Automation.ObjectProofTree

/-! 原rowCheck的纯关系条件：取得实际裸tag，tag=0时按原field0调用准确六类局部表。 -/
namespace PPAC.Migration.Internal.ProofTreeRowLocalSyntax
open Source SourceAlgebra SourceLogic

def fieldCheck {m} (test : Formula 1) (w row z : Fin m) : Formula m := .ex
  ((RawCodeFieldSyntax.field w.castSucc row.castSucc z.castSucc (Fin.last m)).conj (ProofAllNodeSyntax.table test w.castSucc (Fin.last m)))

def atZero {m} (test : Formula 1) (w row : Fin m) : Formula m := .ex
  ((OmegaSyntax.empty (Fin.last m)).conj (fieldCheck test w.castSucc row.castSucc (Fin.last m)))

def localCondition {m} (test : Formula 1) (w row : Fin m) : Formula m := .ex
  ((PairingProjectionSyntax.step true true w.castSucc row.castSucc (Fin.last m)).conj
    ((OmegaSyntax.empty (Fin.last m)).imp (atZero test w.castSucc row.castSucc)))

theorem fieldCheck_rename {m l} (test : Formula 1) (w row z : Fin m) (ρ : Fin m → Fin l) :
    (fieldCheck test w row z).rename ρ = fieldCheck test (ρ w) (ρ row) (ρ z) := by
  simp only [fieldCheck, Formula.rename, RawCodeFieldSyntax.field_rename, ProofAllTableRenaming.table_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem atZero_rename {m l} (test : Formula 1) (w row : Fin m) (ρ : Fin m → Fin l) :
    (atZero test w row).rename ρ = atZero test (ρ w) (ρ row) := by
  simp only [atZero, Formula.rename, OmegaSyntax.empty_rename, fieldCheck_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem localCondition_rename {m l} (test : Formula 1) (w row : Fin m) (ρ : Fin m → Fin l) :
    (localCondition test w row).rename ρ = localCondition test (ρ w) (ρ row) := by
  simp only [localCondition, Formula.rename, PairingProjectionSyntax.step_rename, OmegaSyntax.empty_rename, atZero_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.ProofTreeRowLocalSyntax
