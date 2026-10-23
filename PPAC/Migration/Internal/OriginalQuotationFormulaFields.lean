import PPAC.Migration.Internal.PureQuotationTypedTerms

/-! 已知子quotation及其作用域类型时，原11构造父quotation具有完整FormulaCode类型。 -/
namespace PPAC.Migration.Internal.OriginalQuotationFormulaFields
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalQuotationFieldSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w b f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hn : Derives Γ (tree (leaf (SyntaxAtomSyntax.nullaryTag truth)) w n)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxAtomSyntax.nullaryTag truth) List.nil w n Fin.elim0 hw (.eqRefl w) hn
  exact .impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ truth w b f n hw hc)) ht

theorem equal_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (left right : Tree) (w b f n x y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (tree (.node 3 [left,right]) w n))
    (hx : Derives Γ (tree left w x)) (hy : Derives Γ (tree right w y))
    (hxt : Derives Γ (SyntaxTermSyntax.term w b f x)) (hyt : Derives Γ (SyntaxTermSyntax.term w b f y)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hf : Derives Γ (fields [left,right] w (SyntaxAtomSyntax.two x y)) := .conjI hx (.conjI hy (.eqRefl w))
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ 3 [left,right] w n (SyntaxAtomSyntax.two x y) hw hf hn
  exact .impE (.conjR (FormulaCodeKnownAtomic.equal_iff hZ w b f x y n hw hc)) (.conjI hxt hyt)

theorem member_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (left right : Tree) (w b f n s x y : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (tree (.node 2 [leaf 0,left,right]) w n))
    (hs : Derives Γ (tree (leaf 0) w s)) (hx : Derives Γ (tree left w x)) (hy : Derives Γ (tree right w y))
    (hxt : Derives Γ (SyntaxTermSyntax.term w b f x)) (hyt : Derives Γ (SyntaxTermSyntax.term w b f y)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hf : Derives Γ (fields [leaf 0,left,right] w (SyntaxAtomSyntax.three s x y)) := .conjI hs (.conjI hx (.conjI hy (.eqRefl w)))
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ 2 [leaf 0,left,right] w n (SyntaxAtomSyntax.three s x y) hw hf hn
  have hz := OriginalQuotationNodeFields.tree_to_constructor hZ 0 List.nil w s Fin.elim0 hw (.eqRefl w) hs
  exact .impE (.conjR (FormulaCodeKnownAtomic.member_iff hZ w b f s x y n hw hc)) (.conjI hz (.conjI hxt hyt))

theorem negation_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (body : Tree) (w b f n x : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hn : Derives Γ (tree (.node 4 [body]) w n)) (hx : Derives Γ (tree body w x))
    (hxt : Derives Γ (FormulaCodeSyntax.formulaCode w x b f)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hf : Derives Γ (fields [body] w (fun _ => x)) := .conjI hx (.eqRefl w)
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ 4 [body] w n (fun _ => x) hw hf hn
  exact .impE (.conjR (FormulaCodeKnownLogical.negation_iff hZ w b f x n hw hc)) (.conjI ht hxt)

theorem binary_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (left right : Tree) (w b f n x y : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hn : Derives Γ (tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n))
    (hx : Derives Γ (tree left w x)) (hy : Derives Γ (tree right w y))
    (hxt : Derives Γ (FormulaCodeSyntax.formulaCode w x b f)) (hyt : Derives Γ (FormulaCodeSyntax.formulaCode w y b f)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hf : Derives Γ (fields [left,right] w (SyntaxAtomSyntax.two x y)) := .conjI hx (.conjI hy (.eqRefl w))
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxLogicalSyntax.binaryTag kind) [left,right] w n (SyntaxAtomSyntax.two x y) hw hf hn
  have hi : Derives Γ ((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeBranchSyntax.binaryTypes w b f x y)) := by
    by_cases h0 : kind = 0
    · subst kind; exact FormulaCodeKnownLogical.binary0_iff hZ w b f x y n hw hc
    by_cases h1 : kind = 1
    · subst kind; exact FormulaCodeKnownLogical.binary1_iff hZ w b f x y n hw hc
    by_cases h2 : kind = 2
    · subst kind; exact FormulaCodeKnownLogical.binary2_iff hZ w b f x y n hw hc
    have h3 : kind = 3 := by
      apply Fin.ext
      have hn0 : kind.val ≠ 0 := fun h => h0 (Fin.ext h)
      have hn1 : kind.val ≠ 1 := fun h => h1 (Fin.ext h)
      have hn2 : kind.val ≠ 2 := fun h => h2 (Fin.ext h)
      have hk := kind.isLt
      omega
    subst kind
    exact FormulaCodeKnownLogical.binary3_iff hZ w b f x y n hw hc
  exact .impE (.conjR hi) (.conjI ht (.conjI hxt hyt))

theorem quantified_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (body : Tree) (w b f n x k : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (SyntaxTermSyntax.contexts w b f))
    (hn : Derives Γ (tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n))
    (hx : Derives Γ (tree body w x)) (hk : Derives Γ (successor k b))
    (hxt : Derives Γ (FormulaCodeSyntax.formulaCode w x k f)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  have hf : Derives Γ (fields [body] w (fun _ => x)) := .conjI hx (.eqRefl w)
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ (SyntaxLogicalSyntax.quantifierTag universal) [body] w n (fun _ => x) hw hf hn
  exact .impE (.conjR (FormulaCodeKnownLogical.quantified_iff hZ universal w b f x n k hw hc hk)) (.conjI ht hxt)

end PPAC.Migration.Internal.OriginalQuotationFormulaFields
