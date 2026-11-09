import PPAC.Migration.ForcingGuardCode
import PPAC.Migration.ForcingFormulaAtoms
import PPAC.Migration.Internal.SyntaxForestFieldValues
import PPAC.Migration.Internal.SyntaxVariableImagePoint

/-! The ACTUAL member guard compiler has exactly the original condition term
and the original P free slot. All original compiler/quotation/atom witnesses
are eliminated in the object theory. This does not assert guard truth. -/
namespace PPAC.Migration.ForcingMemberGuard
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private theorem identity_converted_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f I S i Y : Fin m)
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f I))
    (hS : Derives Γ (IndexTermImageCodeSyntax.converted false w I S f a f))
    (hi : Derives Γ (Formula.mem i f)) (hY : Derives Γ (StructuralListFieldSyntax.field w S i Y)) :
    Derives Γ (SyntaxVariableSyntax.code false w i Y) := by
  let E := IndexTermImageCodeSyntax.body false w I S f a f
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hS
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f I (old 2)) (HornBinderRules.under_body 2 hI E)
  have hY2 := of_eq (StructuralListFieldSyntax.field_rename w S i Y (old 2)) (HornBinderRules.under_body 2 hY E)
  have hi2 := HornBinderRules.under_body 2 hi E
  have hdiag := SyntaxIdentityCode.at_graph hZ2 (old 2 w) (old 2 f) (old 2 I) (slot 2 0) hI2 (.conjL hE)
  have hedge := Derives.impE (.conjR (SyntaxMixedImageCodeFields.edges (old 2 w) (slot 2 1) (old 2 f) (old 2 a) (old 2 f) (old 2 S) (old 2 i) (old 2 Y) (.conjR (.conjR hE)))) (.conjI hi2 hY2)
  have hv := Derives.impE (.conjL (SyntaxVariableImageGraph.edge_iff hZ2 false (old 2 w) (slot 2 0) (old 2 f) (old 2 a) (old 2 f) (slot 2 1) (old 2 i) (old 2 Y) (.conjL (.conjR hE)))) hedge
  let B := SyntaxVariableImageSyntax.body false (old 2 w) (slot 2 0) (old 2 a) (old 2 f) (old 2 i) (old 2 Y)
  let Ξ := Context.add B (Context.image Formula.raise Δ)
  apply Derives.exE (p := B) hv
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hd3 := of_eq (SyntaxRenameTermIdentity.diagonal_rename (slot 2 0) Fin.castSucc) (under hdiag B)
  have heq := SyntaxRenameTermIdentity.diagonal_at (slot 2 0).castSucc (old 2 i).castSucc (Fin.last (m+2)) hd3 (.conjL hB)
  exact of_eq (by simp only [Formula.raise, SyntaxVariableSyntax.code_rename])
    (SyntaxVariableImagePoint.code_subst_index false (old 2 w).castSucc (Fin.last (m+2)) (old 2 Y).castSucc (old 2 i).castSucc (eq_symm heq) (.conjL (.conjR hB)))

theorem identity_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a f S i Y : Fin m)
    (hS : Derives Γ (ForcingAtomicCode.identityImages w a f S))
    (hi : Derives Γ (Formula.mem i f)) (hY : Derives Γ (StructuralListFieldSyntax.field w S i Y)) :
    Derives Γ (SyntaxVariableSyntax.code false w i Y) := by
  let B := (SyntaxIdentityMapSyntax.identityCode w.castSucc f.castSucc (Fin.last m)).conj
    (IndexTermImageCodeSyntax.converted false w.castSucc (Fin.last m) S.castSucc f.castSucc a.castSucc f.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hS
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hY1 := of_eq (StructuralListFieldSyntax.field_rename w S i Y Fin.castSucc) (under hY B)
  have hout := identity_converted_field (ZFContext.under hZ B) w.castSucc a.castSucc f.castSucc (Fin.last m) S.castSucc i.castSucc Y.castSucc
    (.conjL hB) (.conjR hB) (under hi B) hY1
  exact of_eq (SyntaxVariableSyntax.code_rename false w i Y Fin.castSucc).symm hout

def data {m} (w x q i sym Y : Fin m) : Formula m :=
  (SyntaxAtomSyntax.zeroScalar w sym).conj ((SyntaxVariableSyntax.code false w i Y).conj
    (SyntaxAtomSyntax.memberCode w sym x Y q))
theorem data_rename {m l} (w x q i sym Y : Fin m) (ρ : Fin m → Fin l) :
    (data w x q i sym Y).rename ρ = data (ρ w) (ρ x) (ρ q) (ρ i) (ρ sym) (ρ Y) := by
  simp only [data, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxVariableSyntax.code_rename, SyntaxAtomSyntax.memberCode_rename]
def body {m} (w x q i : Fin m) : Formula (m+2) := data (old 2 w) (old 2 x) (old 2 q) (old 2 i) (slot 2 0) (slot 2 1)
def result {m} (w x q i : Fin m) : Formula m := existsMany 2 (body w x q i)
theorem result_rename {m l} (w x q i : Fin m) (ρ : Fin m → Fin l) :
    (result w x q i).rename ρ = result (ρ w) (ρ x) (ρ q) (ρ i) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem at_fields {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w z a f x q i sym sx sy : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hv : Derives Γ (ForcingGuardCode.matrix false Reln w a f x q v))
    (hsym : Derives Γ (OriginalTreeQuotationSyntax.tree (leaf 0) w sym))
    (hsx : Derives Γ (OriginalTreeQuotationSyntax.tree (Tree.node 0 ([leaf 0])) w sx))
    (hsy : Derives Γ (OriginalTreeQuotationSyntax.tree (Tree.node 1 ([leaf k])) w sy)) :
    Derives Γ (result w x q i) := by
  have ht : Derives Γ (OriginalTreeQuotationSyntax.tree (Tree.node 2 ([leaf 0, Tree.node 0 ([leaf 0]), Tree.node 1 ([leaf k])])) w (v 1)) :=
    of_eq (congrArg (fun t => OriginalTreeQuotationSyntax.tree t w (v 1)) (ForcingGuardCode.member_template_tree Reln))
      (.conjL (.conjL (.conjR hv)))
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ 2 [leaf 0, Tree.node 0 ([leaf 0]), Tree.node 1 ([leaf k])] w (v 1)
    (SyntaxAtomSyntax.three sym sx sy) hw (.conjI hsym (.conjI hsx (.conjI hsy (.eqRefl w)))) ht
  have hb := OriginalQuotationVariableFields.variable_of_tree hZ true 0 w z sx hw hz hsx
  have hf := OriginalQuotationVariableFields.variable_of_tree hZ false k w i sy hw hi hsy
  have hsubst := Derives.conjR (.conjR (.conjR (.conjR (.conjR hv))))
  have hLists := Derives.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ w (v 2) (v 3) (v 0) f a f (v 1) q hw hsubst)
  have he := ForcingFormulaAtoms.atom_output hZ true w sym (v 2) (v 3) (v 0) f a f (v 1) sx sy q hw hc hsubst
  let E := ForcingFormulaAtoms.atomBody true w sym (v 2) (v 3) (v 0) f a f sx sy q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E)
  have hv2 := of_eq (ForcingGuardCode.matrix_rename false Reln w a f x q v (old 2)) (HornBinderRules.under_body 2 hv E)
  have hb2 := of_eq (SyntaxVariableSyntax.code_rename true w z sx (old 2)) (HornBinderRules.under_body 2 hb E)
  have hf2 := of_eq (SyntaxVariableSyntax.code_rename false w i sy (old 2)) (HornBinderRules.under_body 2 hf E)
  have hl2 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w (v 0) f a f (v 2) (v 3) (old 2)) (HornBinderRules.under_body 2 hLists E)
  have hlft := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ2 true (old 2 w) (old 2 (v 2)) (old 2 (v 3)) (old 2 (v 0)) (old 2 f) (old 2 a) (old 2 f) (old 2 sx) (slot 2 0) (old 2 z) hw2 hl2 hb2)) (.conjL (.conjR hE))
  have hxEq := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ2 1 (old 2 w) (fun _ => old 2 x) (old 2 (v 2)) 0 (old 2 z) (slot 2 0) hw2 (.conjL (.conjR (.conjR hv2))) hz2)) (.conjR hlft)
  have hrgt := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ2 false (old 2 w) (old 2 (v 2)) (old 2 (v 3)) (old 2 (v 0)) (old 2 f) (old 2 a) (old 2 f) (old 2 sy) (slot 2 1) (old 2 i) hw2 hl2 hf2)) (.conjR (.conjR hE))
  have hfree := identity_field hZ2 (old 2 w) (old 2 a) (old 2 f) (old 2 (v 3)) (old 2 i) (slot 2 1)
    (.conjL (.conjR (.conjR (.conjR (.conjR hv2))))) (.conjL hrgt) (.conjR hrgt)
  have hcode := SyntaxRenameAtomicSubst.member_x (old 2 w) (old 2 sym) (slot 2 0) (slot 2 1) (old 2 q) (old 2 x) hxEq (.conjL hE)
  have hs0 : Derives Γ (SyntaxAtomSyntax.zeroScalar w sym) := OriginalQuotationNodeFields.tree_to_constructor hZ 0 [] w sym Fin.elim0 hw (.eqRefl w) hsym
  have hs02 : Derives Δ (SyntaxAtomSyntax.zeroScalar (old 2 w) (old 2 sym)) :=
    of_eq (SyntaxAtomSyntax.zeroScalar_rename w sym (old 2)) (HornBinderRules.under_body 2 hs0 E)
  have hout : Derives Δ (result (old 2 w) (old 2 x) (old 2 q) (old 2 i)) := by
    apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two (old 2 sym) (slot 2 1))
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) (.conjI hs02 (.conjI hfree hcode))
  exact of_eq (result_rename w x q i (old 2)).symm hout

/-- The three literal quotation fields are generated by the existing
original-tree existence theorem, never supplied as code-answer premises. -/
theorem from_matrix {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w z a f x q i : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hv : Derives Γ (ForcingGuardCode.matrix false Reln w a f x q v)) : Derives Γ (result w x q i) := by
  have he0 := OriginalTreeQuotationExistence.tree_exists hZ (leaf 0) w hw
  let E0 := (Formula.mem (Fin.last m) w.castSucc).conj (OriginalTreeQuotationSyntax.tree (leaf 0) w.castSucc (Fin.last m))
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E0
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E0)
  have he1 := OriginalTreeQuotationExistence.tree_exists hZ1 (Tree.node 0 ([leaf 0])) w.castSucc hw1
  let E1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (OriginalTreeQuotationSyntax.tree (Tree.node 0 ([leaf 0])) w.castSucc.castSucc (Fin.last (m+1)))
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 E1
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 E1)
  have he2 := OriginalTreeQuotationExistence.tree_exists hZ2 (Tree.node 1 ([leaf k])) w.castSucc.castSucc hw2
  let E2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (OriginalTreeQuotationSyntax.tree (Tree.node 1 ([leaf k])) w.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Δ3 := Context.add E2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := E2) he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 E2
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 E2)
  have hz3 : Derives Δ3 (empty (old 3 z)) := of_eq (by simp only [Formula.raise, empty_rename]; rfl) (under (under (under hz E0) E1) E2)
  have hi3 : Derives Δ3 (SyntaxNumeralSyntax.numeral k (old 3 i)) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]; rfl) (under (under (under hi E0) E1) E2)
  have hv3 : Derives Δ3 (ForcingGuardCode.matrix false Reln (old 3 w) (old 3 a) (old 3 f) (old 3 x) (old 3 q) (fun j => old 3 (v j))) :=
    of_eq (by simp only [Formula.raise, ForcingGuardCode.matrix_rename]; rfl) (under (under (under hv E0) E1) E2)
  have hs03 : Derives Δ3 (OriginalTreeQuotationSyntax.tree (leaf 0) (old 3 w) (slot 3 0)) :=
    of_eq (by simp only [Formula.raise, OriginalTreeQuotationSyntax.tree_rename]; rfl) (under (under (.conjR hE0) E1) E2)
  have hs13 : Derives Δ3 (OriginalTreeQuotationSyntax.tree (Tree.node 0 ([leaf 0])) (old 3 w) (slot 3 1)) :=
    of_eq (by simp only [Formula.raise, OriginalTreeQuotationSyntax.tree_rename]; rfl) (under (.conjR hE1) E2)
  have hout := at_fields hZ3 Reln (old 3 w) (old 3 z) (old 3 a) (old 3 f) (old 3 x) (old 3 q) (old 3 i)
    (slot 3 0) (slot 3 1) (slot 3 2) (fun j => old 3 (v j)) hw3 hz3 hi3 hv3
    hs03 hs13 (.conjR hE2)
  exact of_eq (by simp only [Formula.raise, result_rename]; rfl) hout

/-- ACTUAL complete guard compilation, with all four compiler witnesses and
three original quotation fields eliminated internally. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w z a f x q i : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hc : Derives Γ (ForcingGuardCode.compiled false Reln w a f x q)) : Derives Γ (result w x q i) := by
  let E := ForcingGuardCode.body false Reln w a f x q
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hout := from_matrix (HornBinderRules.zf_body 4 hZ E) Reln
    (old 4 w) (old 4 z) (old 4 a) (old 4 f) (old 4 x) (old 4 q) (old 4 i) (slot 4)
    (of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw E))
    (of_eq (empty_rename z (old 4)) (HornBinderRules.under_body 4 hz E))
    (of_eq (SyntaxNumeralSyntax.numeral_rename k i (old 4)) (HornBinderRules.under_body 4 hi E)) hE
  exact of_eq (result_rename w x q i (old 4)).symm hout

def input {k m} (Reln : Source.Formula (k+2)) (w z a f x q i : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxNumeralSyntax.numeral k i).conj
    (ForcingGuardCode.compiled false Reln w a f x q)))
def sentence {k m} (Reln : Source.Formula (k+2)) (w z a f x q i : Fin m) : Source.Sentence :=
  ((input Reln w z a f x q i).imp (result w x q i)).close

theorem kernel_certificate {k m} (Reln : Source.Formula (k+2)) (w z a f x q i : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence Reln w z a f x q i)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input Reln w z a f x q i
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_compiled (ZFContext.add (ZFContext.source_ZF m) E) Reln w z a f x q i
    (.conjL h) (.conjL (.conjR h)) (.conjL (.conjR (.conjR h))) (.conjR (.conjR (.conjR h)))

end PPAC.Migration.ForcingMemberGuard
