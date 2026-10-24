import PPAC.Migration.Internal.ProjectCompilerQueryTyping

/-! Actual constant and logical compiler matrices produce target types under object child-query typing. -/
namespace PPAC.Migration.Internal.ProjectCompilerMatrixTyping
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax ProjectCompilerCaseSyntax ProjectCompilerTypingSyntax
open FormulaCodeSyntax FormulaCodeBranchSyntax

theorem constant_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w n b z q : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hc : Derives Γ (constant truth w n q)) : Derives Γ (formulaCode w q b z) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  have ht := Derives.impE (.conjR (FormulaCodeKnownAtomic.nullary_iff hZ truth w b z n hw (.conjL hc))) (.conjI hb hzW)
  exact FormulaCodeTransport.code_root w n b z q (eq_symm (.conjR hc)) ht

theorem single_known_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w b z y q : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode tag w y q)) :
    Derives Γ ((formulaCode w q b z).iff (singleTypes advance w b z y)) := by
  rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact FormulaCodeKnownLogical.negation_iff hZ w b z y q hw hc
  · exact FormulaCodeKnownLogical.forall_iff hZ w b z y q hw hc
  · exact FormulaCodeKnownLogical.exists_iff hZ w b z y q hw hc

theorem binary_known_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w b z X Y q : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w X Y q)) :
    Derives Γ ((formulaCode w q b z).iff (binaryTypes w b z X Y)) := by
  rcases kind with ⟨i,hi⟩
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  · exact FormulaCodeKnownLogical.binary0_iff hZ w b z X Y q hw hc
  · exact FormulaCodeKnownLogical.binary1_iff hZ w b z X Y q hw hc
  · exact FormulaCodeKnownLogical.binary2_iff hZ w b z X Y q hw hc
  · exact FormulaCodeKnownLogical.binary3_iff hZ w b z X Y q hw hc

theorem single_matrix {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b z n q x y : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b z))
    (hg : Derives Γ (goodQueries P ρ w n z)) (hc : Derives Γ (singleMatrix tag advance P ρ w b n q x y)) :
    Derives Γ (formulaCode w q b z) := by
  have ht := ProjectCompilerQueryTyping.check_type advance P ρ w n z x b y hg (.conjL (.conjR hc))
  have hi := single_known_iff hZ tag advance hs w b z y q hw (.conjR (.conjR hc))
  exact .impE (.conjR hi) (.conjI hctx ht)

theorem binary_matrix {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (P : Formula (k+3)) (ρ : Fin k → Fin m) (w b z n q x y X Y : Fin m)
    (hw : Derives Γ (omega w)) (hctx : Derives Γ (SyntaxTermSyntax.contexts w b z))
    (hg : Derives Γ (goodQueries P ρ w n z)) (hc : Derives Γ (binaryMatrix kind P ρ w b n q x y X Y)) :
    Derives Γ (formulaCode w q b z) := by
  have hX := query_type P ρ w n z x b X hg (.conjL (.conjR hc))
  have hY := query_type P ρ w n z y b Y hg (.conjL (.conjR (.conjR hc)))
  have hi := binary_known_iff hZ kind w b z X Y q hw (.conjR (.conjR (.conjR hc)))
  exact .impE (.conjR hi) (.conjI hctx (.conjI hX hY))

end PPAC.Migration.Internal.ProjectCompilerMatrixTyping
