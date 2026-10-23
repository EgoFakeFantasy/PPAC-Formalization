import PPAC.Migration.Internal.TermQuotationSubstitution

/-! 两类实际索引图下的项quotation推进；bound像位移，free像索引不变。 -/
namespace PPAC.Migration.Internal.TermQuotationShiftFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def shiftIndex (isBound : Bool) (k : Nat) : Nat := if isBound then k+1 else k

theorem branch_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (k : Nat)
    (w U V c d C n q i : Fin m) (hw : Derives Γ (omega w))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf k]) w n))
    (hh : Derives Γ (SyntaxRenameTermSyntax.branch isBound w (SyntaxIndexMapSyntax.selectMap isBound U V) (SyntaxTermSyntax.limit isBound c d) n q)) :
    Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf (shiftIndex isBound k)]) w q) := by
  have hc := OriginalQuotationVariableFields.variable_of_tree hZ isBound k w i n hw hi hn
  let B := SyntaxRenameTermSyntax.branchBody isBound w (SyntaxIndexMapSyntax.selectMap isBound U V) (SyntaxTermSyntax.limit isBound c d) n q
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameTermSyntax.eliminate_branch isBound w (SyntaxIndexMapSyntax.selectMap isBound U V) (SyntaxTermSyntax.limit isBound c d) n q _ hh
  have hZ2 := ZFContext.under_two hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (OrderedPairElimination.under_two hw B)
  have hc2 : Derives Δ (SyntaxVariableSyntax.code isBound w.castSucc.castSucc i.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxVariableSyntax.code_rename]) (OrderedPairElimination.under_two hc B)
  have hi2 : Derives Δ (SyntaxNumeralSyntax.numeral k i.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (OrderedPairElimination.under_two hi B)
  have hU2 : Derives Δ (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc c.castSucc.castSucc C.castSucc.castSucc U.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxFreeShiftSyntax.shiftMap_rename]) (OrderedPairElimination.under_two hU B)
  have hV2 : Derives Δ (SyntaxIdentityMapSyntax.identityMap w.castSucc.castSucc d.castSucc.castSucc V.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxIdentityMapSyntax.identityMap_rename]) (OrderedPairElimination.under_two hV B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := SyntaxVariableDecode.index_eq hZ2 isBound w.castSucc.castSucc (Fin.last m).castSucc i.castSucc.castSucc n.castSucc.castSucc hw2 (.conjL (.conjR (.conjR hB))) hc2
  have hnum := SyntaxNumeralSyntax.output_subst k i.castSucc.castSucc (Fin.last m).castSucc (eq_symm he) hi2
  have hj : Derives Δ (SyntaxNumeralSyntax.numeral (shiftIndex isBound k) (Fin.last (m+1))) := by
    cases isBound
    · have heq := SyntaxRenameTermIdentity.diagonal_at V.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjR hV2) (.conjL (.conjR hB))
      exact SyntaxNumeralSyntax.output_subst k _ _ heq hnum
    · have hg := SyntaxFreeShiftGraph.to_graph _ _ _ _ hU2
      have hs := Derives.conjR (Derives.impE (.conjL (SyntaxFreeShiftGraph.edge_iff _ _ _ _ hg)) (.conjL (.conjR hB)))
      exact SyntaxNumeralSyntax.intro_succ k _ _ hnum hs
  have ho := OriginalQuotationVariableFields.tree_of_variable isBound (shiftIndex isBound k) w.castSucc.castSucc (Fin.last (m+1)) q.castSucc.castSucc hj (.conjR (.conjR (.conjR hB)))
  exact of_eq (by simp only [Formula.raise, OriginalTreeQuotationSyntax.tree_rename]) ho

theorem renamed_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (k : Nat)
    (w U V c d C n q i : Fin m) (hw : Derives Γ (omega w))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hn : Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf k]) w n))
    (hh : Derives Γ (SyntaxRenameTermSyntax.renamed w U V c d C d n q)) :
    Derives Γ (OriginalTreeQuotationSyntax.tree (.node (SyntaxVariableSyntax.tag isBound) [leaf (shiftIndex isBound k)]) w q) := by
  have hc := OriginalQuotationVariableFields.variable_of_tree hZ isBound k w i n hw hi hn
  cases isBound
  · apply Derives.disjE (.conjR hh)
    · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ _) false w c n i (add hw _) (add hc _) (SyntaxRenameTermTyping.source_branch true w U c n q (.hyp (Or.inl rfl))))
    · exact branch_forward (ZFContext.add hZ _) false k w U V c d C n q i (add hw _) (add hU _) (add hV _) (add hi _) (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.disjE (.conjR hh)
    · exact branch_forward (ZFContext.add hZ _) true k w U V c d C n q i (add hw _) (add hU _) (add hV _) (add hi _) (add hn _) (.hyp (Or.inl rfl))
    · exact .botE (SyntaxTermBranches.opposite (ZFContext.add hZ _) true w d n i (add hw _) (add hc _) (SyntaxRenameTermTyping.source_branch false w V d n q (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.TermQuotationShiftFields
