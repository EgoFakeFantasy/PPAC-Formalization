import PPAC.Migration.Internal.SyntaxRenameSystemSyntax

/-! 实际内部ω、幂集载体和原递归族连同所有内部参数的完整RenameFormula递归定律。 -/
namespace PPAC.Migration.Internal.SyntaxRenameSystem
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameSystemSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (universalLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  let Δ : Context (m+8) := Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Γ))))))))
  have hZ8 : ZFContext.Evidence Δ := ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (ZFContext.rename (hZ) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc) Fin.castSucc
  have hw8 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc (hw)))))))))
  exact SyntaxRenameRecursive.recursive_iff hZ8 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc (Fin.last (m+6)).castSucc (Fin.last (m+7)) hw8

theorem actual_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ (system w) := .conjI (SyntaxRenameRecursors.actual_carrier_recursors hZ w) (all_law hZ w hw)

theorem existence {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) : Derives Γ (existsSystem.rename Fin.elim0) := by
  have he := ZFContext.closed hZ ObjectOmega.source_ZF_existence
  let W := omega (Fin.last m)
  let Δ := Context.add W (Context.image Formula.raise Γ)
  change Derives Γ (.ex W) at he
  apply Derives.exE (p := W) he
  have hW : Derives Δ W := .hyp (Or.inl rfl)
  have hs := actual_system (ZFContext.under hZ W) (Fin.last m) hW
  have ho : Derives Δ (existsSystem.rename Fin.elim0) := by
    simp only [existsSystem, Formula.rename, omega_rename, system_rename, Formula.liftRen, Fin.lastCases_last]
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [W, Formula.instantiate, Formula.rename, omega_rename, system_rename, Fin.lastCases_last]) (.conjI hW hs)
  exact of_eq (closed_rename existsSystem Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxRenameSystem
