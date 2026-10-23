import PPAC.Migration.PureSyntaxOperations
import PPAC.Migration.Internal.OriginalTreeQuotationFiber

/-! 纯语言内在语法的紧凑数值quotation模式及实际内部码纤维；外部AST模式不代表全部内部公式码的操作正确性。 -/
namespace PPAC.Migration.Internal.PureQuotationSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory

def term {m} {bound free : PureSyntaxQuotation.Ctx} {sort : SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) : Source.Formula m :=
  OriginalTreeQuotationSyntax.tree (PureSyntaxQuotation.termTree input) w n

def formula {m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) : Source.Formula m :=
  OriginalTreeQuotationSyntax.tree (PureSyntaxQuotation.formulaTree input) w n

theorem term_eq_original {m} {bound free : PureSyntaxQuotation.Ctx} {sort : SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) :
    OriginalTreeQuotationSyntax.tree (FirstOrder.FormalSystem.ProofT.SyntaxEncode.term (PureSyntaxQuotation.term input)) w n = term input w n :=
  congrArg (fun t => OriginalTreeQuotationSyntax.tree t w n) (PureSyntaxQuotation.term_encoding input)

theorem formula_eq_original {m} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) :
    OriginalTreeQuotationSyntax.tree (FirstOrder.FormalSystem.ProofT.SyntaxEncode.formula (PureSyntaxQuotation.formula input)) w n = formula input w n :=
  congrArg (fun t => OriginalTreeQuotationSyntax.tree t w n) (PureSyntaxQuotation.formula_encoding input)

theorem term_rename {m k} {bound free : PureSyntaxQuotation.Ctx} {sort : SetSort}
    (input : PureSyntaxQuotation.Tm bound free sort) (w n : Fin m) (ρ : Fin m → Fin k) :
    (term input w n).rename ρ = term input (ρ w) (ρ n) := OriginalTreeQuotationSyntax.tree_rename _ w n ρ

theorem formula_rename {m k} {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound free) (w n : Fin m) (ρ : Fin m → Fin k) :
    (formula input w n).rename ρ = formula input (ρ w) (ρ n) := OriginalTreeQuotationSyntax.tree_rename _ w n ρ

theorem term_unique {m} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} {sort : SetSort} (input : PureSyntaxQuotation.Tm bound free sort) (w n v : Fin m)
    (hw : Source.Derives Γ (omega w)) (hn : Source.Derives Γ (term input w n)) (hv : Source.Derives Γ (term input w v)) : Source.Derives Γ (.equal n v) :=
  OriginalTreeQuotationUnique.tree_unique hZ _ w n v hw hn hv

theorem formula_unique {m} {Γ : Source.Context m} (hZ : ZFContext.Evidence Γ)
    {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound free) (w n v : Fin m)
    (hw : Source.Derives Γ (omega w)) (hn : Source.Derives Γ (formula input w n)) (hv : Source.Derives Γ (formula input w v)) : Source.Derives Γ (.equal n v) :=
  OriginalTreeQuotationUnique.tree_unique hZ _ w n v hw hn hv

end PPAC.Migration.Internal.PureQuotationSyntax
