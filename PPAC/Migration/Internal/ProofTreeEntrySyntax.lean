import PPAC.Migration.Internal.ProofTreeBranchConstruction

/-! 原node0[code]与root1[code,conclusion]入口；根关闭性／可靠性归纳另需证明。 -/
namespace PPAC.Migration.Internal.ProofTreeEntrySyntax
open Source SourceAlgebra SourceLogic

def node {m} (test : Formula 1) (w code : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 1 0 w.castSucc (fun _ => code.castSucc) (Fin.last m)).conj
    (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m)))

def root {m} (test : Formula 1) (w code conclusion : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 2 1 w.castSucc (SetLanguage.args2 code.castSucc conclusion.castSucc) (Fin.last m)).conj
    (ProofTreeTraceSyntax.condition test w.castSucc (Fin.last m)))

def nodeEquation {m} (test : Formula 1) (w code : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 1 0 w.castSucc (fun _ => code.castSucc) (Fin.last m)).conj
    (ProofTreeTraceEquation.equation test w.castSucc (Fin.last m)))

def rootEquation {m} (test : Formula 1) (w code conclusion : Fin m) : Formula m := .ex
  ((SyntaxNodeSyntax.constructor 2 1 w.castSucc (SetLanguage.args2 code.castSucc conclusion.castSucc) (Fin.last m)).conj
    (ProofTreeTraceEquation.equation test w.castSucc (Fin.last m)))

theorem node_recursive_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code : Fin m) :
    Derives Γ ((node test w code).iff (nodeEquation test w code)) := by
  apply FormulaCodeCongruence.ex_congr
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (ProofTreeTraceEquation.recursive_iff test (HornBinderRules.zf_many 1 hZ) w.castSucc (Fin.last m))

theorem root_recursive_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w code conclusion : Fin m) :
    Derives Γ ((root test w code conclusion).iff (rootEquation test w code conclusion)) := by
  apply FormulaCodeCongruence.ex_congr
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (ProofTreeTraceEquation.recursive_iff test (HornBinderRules.zf_many 1 hZ) w.castSucc (Fin.last m))

end PPAC.Migration.Internal.ProofTreeEntrySyntax
