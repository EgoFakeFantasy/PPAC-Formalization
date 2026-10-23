import PPAC.Migration.Internal.FormulaQuotationAtomicSteps

/-! 原逻辑构造quotation与实际子混合判断组合；量词要求真实原双表提升而非宿主替换等式。 -/
namespace PPAC.Migration.Internal.FormulaQuotationLogicalSteps
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax OriginalQuotationFieldSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem negation {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (body targetBody : Tree)
    (w R S a b c d n q x X : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hn : Derives Γ (tree (.node 4 [body]) w n)) (hq : Derives Γ (tree (.node 4 [targetBody]) w q))
    (hx : Derives Γ (tree body w x)) (hX : Derives Γ (tree targetBody w X))
    (hs : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := by
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ 4 [body] w n (fun _ => x) hw (.conjI hx (.eqRefl w)) hn
  have hd := OriginalQuotationNodeFields.tree_to_constructor hZ 4 [targetBody] w q (fun _ => X) hw (.conjI hX (.eqRefl w)) hq
  exact .impE (.conjR (SyntaxMixedFormulaEndpoints.single_iff hZ 4 false (Or.inl ⟨rfl,rfl⟩) w R S a b c d n q x X hw hi hc hd)) hs

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (left right targetLeft targetRight : Tree)
    (w R S a b c d n q x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hn : Derives Γ (tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n))
    (hq : Derives Γ (tree (.node (SyntaxLogicalSyntax.binaryTag kind) [targetLeft,targetRight]) w q))
    (hx : Derives Γ (tree left w x)) (hy : Derives Γ (tree right w y))
    (hX : Derives Γ (tree targetLeft w X)) (hY : Derives Γ (tree targetRight w Y))
    (hsx : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X))
    (hsy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d y Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := by
  have hf : Derives Γ (fields [left,right] w (SyntaxAtomSyntax.two x y)) := .conjI hx (.conjI hy (.eqRefl w))
  have hF : Derives Γ (fields [targetLeft,targetRight] w (SyntaxAtomSyntax.two X Y)) := .conjI hX (.conjI hY (.eqRefl w))
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxLogicalSyntax.binaryTag kind) [left,right] w n (SyntaxAtomSyntax.two x y) hw hf hn
  have hd := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxLogicalSyntax.binaryTag kind) [targetLeft,targetRight] w q (SyntaxAtomSyntax.two X Y) hw hF hq
  exact .impE (.conjR (SyntaxMixedFormulaEndpoints.binary_iff hZ kind w R S a b c d n q x y X Y hw hi hc hd)) (.conjI hsx hsy)

theorem quantified {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (body targetBody : Tree)
    (w R S a b c d n q x X A C K H : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hn : Derives Γ (tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n))
    (hq : Derives Γ (tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [targetBody]) w q))
    (hx : Derives Γ (tree body w x)) (hX : Derives Γ (tree targetBody w X))
    (hs : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x X)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q) := by
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxLogicalSyntax.quantifierTag universal) [body] w n (fun _ => x) hw (.conjI hx (.eqRefl w)) hn
  have hd := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxLogicalSyntax.quantifierTag universal) [targetBody] w q (fun _ => X) hw (.conjI hX (.eqRefl w)) hq
  exact .impE (.conjR (SyntaxMixedFormulaEndpoints.quantified_at_lift hZ universal w R S a b c d n q x X A C K H hw hi hl hc hd)) hs

end PPAC.Migration.Internal.FormulaQuotationLogicalSteps
