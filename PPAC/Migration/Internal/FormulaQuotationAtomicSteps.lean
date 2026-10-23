import PPAC.Migration.Internal.NativeTermQuotationSubstitution

/-! 原公式quotation的实际原子构造步骤；准确原字段与混合项判断给出原混合公式推导。 -/
namespace PPAC.Migration.Internal.FormulaQuotationAtomicSteps
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax OriginalQuotationFieldSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hn : Derives Γ (tree (leaf (SyntaxAtomSyntax.nullaryTag truth)) w n))
    (hq : Derives Γ (tree (leaf (SyntaxAtomSyntax.nullaryTag truth)) w q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := by
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxAtomSyntax.nullaryTag truth) List.nil w n Fin.elim0 hw (.eqRefl w) hn
  have heq := OriginalTreeQuotationUnique.tree_unique hZ (leaf (SyntaxAtomSyntax.nullaryTag truth)) w q n hw hq hn
  exact .impE (.conjR (SyntaxMixedFormulaEndpoints.nullary_iff hZ truth w R S a b c d n q hw hi hc)) heq

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (left right targetLeft targetRight : Tree)
    (w R S a b c d n q x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hn : Derives Γ (tree (.node 3 [left,right]) w n)) (hq : Derives Γ (tree (.node 3 [targetLeft,targetRight]) w q))
    (hx : Derives Γ (tree left w x)) (hy : Derives Γ (tree right w y))
    (hX : Derives Γ (tree targetLeft w X)) (hY : Derives Γ (tree targetRight w Y))
    (hsx : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X))
    (hsy : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := by
  have hf : Derives Γ (fields [left,right] w (SyntaxAtomSyntax.two x y)) := .conjI hx (.conjI hy (.eqRefl w))
  have hF : Derives Γ (fields [targetLeft,targetRight] w (SyntaxAtomSyntax.two X Y)) := .conjI hX (.conjI hY (.eqRefl w))
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ 3 [left,right] w n (SyntaxAtomSyntax.two x y) hw hf hn
  have hd := OriginalQuotationNodeFields.tree_to_constructor hZ 3 [targetLeft,targetRight] w q (SyntaxAtomSyntax.two X Y) hw hF hq
  exact .impE (.conjR (SyntaxMixedFormulaEndpoints.equality_iff hZ w R S a b c d n q x y X Y hw hi hc hd)) (.conjI hsx hsy)

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (left right targetLeft targetRight : Tree)
    (w R S a b c d n q s x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hn : Derives Γ (tree (.node 2 [leaf 0,left,right]) w n)) (hq : Derives Γ (tree (.node 2 [leaf 0,targetLeft,targetRight]) w q))
    (hs : Derives Γ (tree (leaf 0) w s)) (hx : Derives Γ (tree left w x)) (hy : Derives Γ (tree right w y))
    (hX : Derives Γ (tree targetLeft w X)) (hY : Derives Γ (tree targetRight w Y))
    (hsx : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X))
    (hsy : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := by
  have hf : Derives Γ (fields [leaf 0,left,right] w (SyntaxAtomSyntax.three s x y)) := .conjI hs (.conjI hx (.conjI hy (.eqRefl w)))
  have hF : Derives Γ (fields [leaf 0,targetLeft,targetRight] w (SyntaxAtomSyntax.three s X Y)) := .conjI hs (.conjI hX (.conjI hY (.eqRefl w)))
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ 2 [leaf 0,left,right] w n (SyntaxAtomSyntax.three s x y) hw hf hn
  have hd := OriginalQuotationNodeFields.tree_to_constructor hZ 2 [leaf 0,targetLeft,targetRight] w q (SyntaxAtomSyntax.three s X Y) hw hF hq
  have hz := OriginalQuotationNodeFields.tree_to_constructor hZ 0 List.nil w s Fin.elim0 hw (.eqRefl w) hs
  exact .impE (.conjR (SyntaxMixedFormulaEndpoints.membership_iff hZ w R S a b c d n q s s x y X Y hw hi hc hd)) (.conjI hz (.conjI (.eqRefl s) (.conjI hsx hsy)))

end PPAC.Migration.Internal.FormulaQuotationAtomicSteps
