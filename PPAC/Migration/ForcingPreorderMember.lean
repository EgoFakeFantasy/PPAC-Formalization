import PPAC.Migration.ForcingPreorderLeafTarget

/-! Identify the SAME actual raw member leaf with the existing original
member-guard opening. Literal quotation fields are generated internally by
the original tree existence theorem; runtime scopes and codes stay internal. -/
namespace PPAC.Migration.ForcingPreorderMember
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedFormulaJudgmentSyntax (substituted substituted_rename)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature
attribute [local irreducible] NaturalRecursionSyntax.matrix

def memberPosition (i : Fin 3) : Fin 6 := i.castAdd 3
def boundIndex (i : Fin 3) : Fin 3 := Fin.cases 2 (Fin.cases 1 (fun _ => 0)) i
def memberTree (k : Nat) (j : Fin 3) : Tree :=
  Tree.node 2 ([leaf 0, Tree.node 0 ([leaf j.val]), Tree.node 1 ([leaf k])])

theorem raw_tree {k} (R : Source.Formula (k+2)) (i : Fin 3) :
    PureSyntaxQuotation.formulaTree (ForcingPreorderCode.atoms R (memberPosition i)) = memberTree k (boundIndex i) := by
  have hIndex : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (Fin.last k).castSucc).index = k :=
    ProjectNativeRenaming.variable_index (fun _ : Fin 1 => (Fin.last k).castSucc)
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (0 : Fin 1))
  rcases i with ⟨i,hi⟩
  have hCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hCases with rfl | rfl | rfl
  · change PureSyntaxQuotation.formulaTree (ForcingPreorderCode.atoms R 0) = _
    rw [ForcingPreorderCode.atom_member_r]
    simp only [PureSyntaxQuotation.formulaTree, PureSyntaxQuotation.argumentTrees, PureSyntaxQuotation.termTree, hIndex]
    rfl
  · change PureSyntaxQuotation.formulaTree (ForcingPreorderCode.atoms R 1) = _
    rw [ForcingPreorderCode.atom_member_q]
    simp only [PureSyntaxQuotation.formulaTree, PureSyntaxQuotation.argumentTrees, PureSyntaxQuotation.termTree, hIndex]
    rfl
  · change PureSyntaxQuotation.formulaTree (ForcingPreorderCode.atoms R 2) = _
    rw [ForcingPreorderCode.atom_member_p]
    simp only [PureSyntaxQuotation.formulaTree, PureSyntaxQuotation.argumentTrees, PureSyntaxQuotation.termTree, hIndex]
    rfl

private structure Inputs {m} (Γ : Context m) (k : Nat) (j : Fin 3)
    (w J I D S A3 f z T n q V : Fin m) (xs : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hw : Derives Γ (omega w)
  hj : Derives Γ (SyntaxNumeralSyntax.numeral j.val J)
  hi : Derives Γ (SyntaxNumeralSyntax.numeral k I)
  ht : Derives Γ (OriginalTreeQuotationSyntax.tree (memberTree k j) w n)
  hf : Derives Γ (SyntaxForestSyntax.forest 3 w xs D)
  hv : Derives Γ (StructuralListFieldSyntax.field w S I V)
  hq : Derives Γ (substituted w D S A3 f z T n q)

private theorem Inputs.in_body {m l} {Γ : Context m} {k} {j : Fin 3}
    {w J I D S A3 f z T n q V : Fin m} {xs : Fin 3 → Fin m}
    (h : Inputs Γ k j w J I D S A3 f z T n q V xs) (E : Formula (m+l)) :
    Inputs (Context.add E (raisedContext l Γ)) k j (old l w) (old l J) (old l I) (old l D) (old l S)
      (old l A3) (old l f) (old l z) (old l T) (old l n) (old l q) (old l V) (fun i => old l (xs i)) := by
  exact ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (omega_rename w (old l)) (HornBinderRules.under_body l h.hw E),
    of_eq (SyntaxNumeralSyntax.numeral_rename j.val J (old l)) (HornBinderRules.under_body l h.hj E),
    of_eq (SyntaxNumeralSyntax.numeral_rename k I (old l)) (HornBinderRules.under_body l h.hi E),
    of_eq (OriginalTreeQuotationSyntax.tree_rename (memberTree k j) w n (old l)) (HornBinderRules.under_body l h.ht E),
    of_eq (SyntaxForestSyntax.forest_rename 3 w xs D (old l)) (HornBinderRules.under_body l h.hf E),
    of_eq (StructuralListFieldSyntax.field_rename w S I V (old l)) (HornBinderRules.under_body l h.hv E),
    of_eq (substituted_rename w D S A3 f z T n q (old l)) (HornBinderRules.under_body l h.hq E)⟩

private theorem at_fields {k m} {Γ : Context m} (j : Fin 3)
    (w J I D S A3 f z T n q V sym bx fy : Fin m) (xs : Fin 3 → Fin m)
    (h : Inputs Γ k j w J I D S A3 f z T n q V xs)
    (hs : Derives Γ (OriginalTreeQuotationSyntax.tree (leaf 0) w sym))
    (hb : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 0 [leaf j.val]) w bx))
    (hf : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 1 [leaf k]) w fy)) :
    Derives Γ (ForcingMemberGuardOpening.result w (xs j) V q) := by
  have hc := OriginalQuotationNodeFields.tree_to_constructor h.zf 2
    [leaf 0, Tree.node 0 ([leaf j.val]), Tree.node 1 ([leaf k])] w n (SyntaxAtomSyntax.three sym bx fy) h.hw
    (.conjI hs (.conjI hb (.conjI hf (.eqRefl w)))) h.ht
  have hBound := OriginalQuotationVariableFields.variable_of_tree h.zf true j.val w J bx h.hw h.hj hb
  have hFree := OriginalQuotationVariableFields.variable_of_tree h.zf false k w I fy h.hw h.hi hf
  have hLists := Derives.conjR (SyntaxMixedFormulaOutput.input_of_substituted h.zf w D S A3 f z T n q h.hw h.hq)
  have he := ForcingFormulaAtoms.atom_output h.zf true w sym D S A3 f z T n bx fy q h.hw hc h.hq
  let E := ForcingFormulaAtoms.atomBody true w sym D S A3 f z T bx fy q
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h2 := h.in_body E
  have hb2 := of_eq (SyntaxVariableSyntax.code_rename true w J bx (old 2)) (HornBinderRules.under_body 2 hBound E)
  have hf2 := of_eq (SyntaxVariableSyntax.code_rename false w I fy (old 2)) (HornBinderRules.under_body 2 hFree E)
  have hl2 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w A3 f z T D S (old 2)) (HornBinderRules.under_body 2 hLists E)
  have hLeft := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h2.zf true
    (old 2 w) (old 2 D) (old 2 S) (old 2 A3) (old 2 f) (old 2 z) (old 2 T) (old 2 bx) (slot 2 0) (old 2 J)
    h2.hw hl2 hb2)) (.conjL (.conjR hE))
  have hX := Derives.impE (.conjL (SyntaxForestFieldValues.field_at h2.zf 3 (old 2 w)
    (fun i => old 2 (xs i)) (old 2 D) j (old 2 J) (slot 2 0) h2.hw h2.hf h2.hj)) (.conjR hLeft)
  have hRight := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h2.zf false
    (old 2 w) (old 2 D) (old 2 S) (old 2 A3) (old 2 f) (old 2 z) (old 2 T) (old 2 fy) (slot 2 1) (old 2 I)
    h2.hw hl2 hf2)) (.conjR (.conjR hE))
  have hIW := SyntaxNumerals.range h2.zf k (old 2 w) (old 2 I) h2.hw h2.hi
  have hY := StructuralListFieldValues.unique h2.zf (old 2 w) (old 2 S) (old 2 I) (slot 2 1) (old 2 V)
    h2.hw hIW (.conjR hRight) h2.hv
  have hCode := SyntaxRenameAtomicSubst.member_y (old 2 w) (old 2 sym) (old 2 (xs j)) (slot 2 1) (old 2 q) (old 2 V) hY
    (SyntaxRenameAtomicSubst.member_x (old 2 w) (old 2 sym) (slot 2 0) (slot 2 1) (old 2 q) (old 2 (xs j)) hX (.conjL hE))
  have hs0 := OriginalQuotationNodeFields.tree_to_constructor h.zf 0 [] w sym Fin.elim0 h.hw (.eqRefl w) hs
  have hs2 := of_eq (SyntaxAtomSyntax.zeroScalar_rename w sym (old 2)) (HornBinderRules.under_body 2 hs0 E)
  have hout : Derives Δ (ForcingMemberGuardOpening.result (old 2 w) (old 2 (xs j)) (old 2 V) (old 2 q)) := by
    apply Derives.exI (old 2 sym)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename,
      SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hs2 hCode)
  exact of_eq (ForcingMemberGuardOpening.result_rename w (xs j) V q (old 2)).symm hout


/-- Decode the actual raw member query. All three quotation child codes
are generated with the existing original-tree existence theorem. -/
theorem raw_member {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (j : Fin 3)
    (w J I D S A3 f z T n q V : Fin m) (xs : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hj : Derives Γ (SyntaxNumeralSyntax.numeral j.val J))
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (ht : Derives Γ (OriginalTreeQuotationSyntax.tree (memberTree k j) w n))
    (hForest : Derives Γ (SyntaxForestSyntax.forest 3 w xs D))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S I V))
    (hq : Derives Γ (substituted w D S A3 f z T n q)) :
    Derives Γ (ForcingMemberGuardOpening.result w (xs j) V q) := by
  have h : Inputs Γ k j w J I D S A3 f z T n q V xs := ⟨hZ,hw,hj,hi,ht,hForest,hv,hq⟩
  have he0 := OriginalTreeQuotationExistence.tree_exists hZ (leaf 0) w hw
  let E0 := (Formula.mem (Fin.last m) w.castSucc).conj (OriginalTreeQuotationSyntax.tree (leaf 0) w.castSucc (Fin.last m))
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) he0
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have h1 := h.in_body E0
  have he1 := OriginalTreeQuotationExistence.tree_exists h1.zf (.node 0 [leaf j.val]) w.castSucc h1.hw
  let E1 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (OriginalTreeQuotationSyntax.tree (.node 0 [leaf j.val]) w.castSucc.castSucc (Fin.last (m+1)))
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) he1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have h2 := h1.in_body E1
  have he2 := OriginalTreeQuotationExistence.tree_exists h2.zf (.node 1 [leaf k]) w.castSucc.castSucc h2.hw
  let E2 := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (OriginalTreeQuotationSyntax.tree (.node 1 [leaf k]) w.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Δ3 := Context.add E2 (Context.image Formula.raise Δ2)
  apply Derives.exE (p := E2) he2
  have hE2 : Derives Δ3 E2 := .hyp (Or.inl rfl)
  have h3 := h2.in_body E2
  have hs3 : Derives Δ3 (OriginalTreeQuotationSyntax.tree (leaf 0) (old 3 w) (slot 3 0)) :=
    of_eq (by simp only [Formula.raise, OriginalTreeQuotationSyntax.tree_rename]; rfl) (under (under (.conjR hE0) E1) E2)
  have hb3 : Derives Δ3 (OriginalTreeQuotationSyntax.tree (.node 0 [leaf j.val]) (old 3 w) (slot 3 1)) :=
    of_eq (by simp only [Formula.raise, OriginalTreeQuotationSyntax.tree_rename]; rfl) (under (.conjR hE1) E2)
  have hout := at_fields j (old 3 w) (old 3 J) (old 3 I) (old 3 D) (old 3 S)
    (old 3 A3) (old 3 f) (old 3 z) (old 3 T) (old 3 n) (old 3 q) (old 3 V)
    (slot 3 0) (slot 3 1) (slot 3 2) (fun i => old 3 (xs i)) h3 hs3 hb3 (.conjR hE2)
  exact of_eq (by simp only [Formula.raise, ForcingMemberGuardOpening.result_rename]; rfl) hout

theorem member_quote {k m} {Γ : Context m} (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f : Fin m) (v : Fin 16 → Fin m)
    (hr : Derives Γ (ForcingPreorderCode.rawData R w z A1 A2 A3 f v)) :
    Derives Γ (OriginalTreeQuotationSyntax.tree (memberTree k (boundIndex i)) w
      (v (ForcingPreorderLeaves.leafSlot (memberPosition i)))) := by
  have ht : Derives Γ (PureQuotationSyntax.formula (ForcingPreorderCode.atoms R (memberPosition i)) w
      (v (ForcingPreorderLeaves.leafSlot (memberPosition i)))) := by
    rcases i with ⟨i,hi⟩
    have hCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hCases with rfl | rfl | rfl
    · exact .conjL (.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hr))))))))))))
    · exact .conjL (.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hr)))))))))))))
    · exact .conjL (.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hr))))))))))))))
  exact of_eq (congrArg (fun t => OriginalTreeQuotationSyntax.tree t w
    (v (ForcingPreorderLeaves.leafSlot (memberPosition i)))) (raw_tree R i)) ht

private def quad {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))
private def indices {m} (z A1 A2 : Fin m) : Fin 3 → Fin m := Fin.cases z (Fin.cases A1 (fun _ => A2))
private theorem at_numeral {m} {Γ : Context m} (j : Fin 3) (z A1 A2 : Fin m)
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2)) :
    Derives Γ (SyntaxNumeralSyntax.numeral j.val (indices z A1 A2 j)) := by
  exact Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun i => Fin.elim0 i))) j

theorem reversed_bound {m} (P : Fin 3 → Fin m) (i : Fin 3) :
    ForcingRelationRawTerms.reversed P (boundIndex i) = P i := by
  rcases i with ⟨i,hi⟩
  have hCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> rfl

/-- SAME generated row supplies its own raw quote, actual query, forest,
condition-code range and original empty-table type. -/
theorem raw_from_data {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I V : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hv : Derives Γ (StructuralListFieldSyntax.field w S I V)) :
    Derives Γ (ForcingMemberGuardOpening.result w (P i) V (H (memberPosition i))) := by
  have hr := Derives.conjL hd
  have hRow := Derives.conjL (Derives.conjL (Derives.conjR hd))
  have hParent := Derives.conjL (Derives.conjR (Derives.conjR hd))
  have hPrefix := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hd)))
  have hQueries := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hd)))
  have hB := Derives.conjL (Derives.conjL (SyntaxMixedFormulaJudgmentTyping.input_of_substituted hZ w B S z f z T (v 2) (U 0) hw hParent))
  have hP := ForcingPreorderLeaves.conditions_natural hZ w z T C Refl Pre Gb H U F P N hw hRow
  have hForest := ForcingRelationRawTerms.forest_from_prefix hZ w z f T B S
    (quad z A1 A2 A3) (quad (v 2) (v 3) (v 4) (v 5)) (quad (U 0) (U 1) (U 2) (N 0)) P D hz hB hP hPrefix
  have hQuote := member_quote R i w z A1 A2 A3 f v hr
  have hQuery := ForcingPreorderLeaves.leaf_at w (D 2) S A3 f z T v H N (memberPosition i) hQueries
  have hout := raw_member hZ (boundIndex i) w (indices z A1 A2 (boundIndex i)) I (D 2) S A3 f z T
    (v (ForcingPreorderLeaves.leafSlot (memberPosition i))) (H (memberPosition i)) V (ForcingRelationRawTerms.reversed P)
    hw (at_numeral (boundIndex i) z A1 A2 hz hA1 hA2) hI hQuote hForest hv hQuery
  exact of_eq (by rw [reversed_bound]) hout

/-- Compare literal member outputs using the original symbol and
constructor uniqueness proofs, without assuming either output equality. -/
theorem same_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P V n q : Fin m)
    (hw : Derives Γ (omega w))
    (hn : Derives Γ (ForcingMemberGuardOpening.result w P V n))
    (hq : Derives Γ (ForcingMemberGuardOpening.result w P V q)) : Derives Γ (.equal n q) := by
  let E0 := (SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) P.castSucc V.castSucc n.castSucc)
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) hn
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have hq1 := of_eq (ForcingMemberGuardOpening.result_rename w P V q Fin.castSucc) (under hq E0)
  let E1 := (SyntaxAtomSyntax.zeroScalar w.castSucc.castSucc (Fin.last (m+1))).conj
    (SyntaxAtomSyntax.memberCode w.castSucc.castSucc (Fin.last (m+1)) P.castSucc.castSucc V.castSucc.castSucc q.castSucc.castSucc)
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) hq1
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ E0) E1
  have hw2 : Derives Δ2 (omega (old 2 w)) := of_eq (by simp only [Formula.raise, omega_rename]; rfl) (under (under hw E0) E1)
  have hOld : Derives Δ2 ((SyntaxAtomSyntax.zeroScalar (old 2 w) (Fin.last m).castSucc).conj
      (SyntaxAtomSyntax.memberCode (old 2 w) (Fin.last m).castSucc (old 2 P) (old 2 V) (old 2 n))) :=
    of_eq (by simp only [E0, Formula.raise, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename]; rfl) (under hE0 E1)
  have he := SyntaxZeroScalar.unique hZ2 (old 2 w) (Fin.last (m+1)) (Fin.last m).castSucc hw2 (.conjL hE1) (.conjL hOld)
  have hc := SyntaxAtomUnique.symbol_subst (old 2 w) (Fin.last (m+1)) (Fin.last m).castSucc (old 2 P) (old 2 V) (old 2 q) he (.conjR hE1)
  exact SyntaxConstructors.unique hZ2 3 2 (old 2 w) (SyntaxAtomSyntax.three (Fin.last m).castSucc (old 2 P) (old 2 V))
    (old 2 n) (old 2 q) hw2 (.conjR hOld) hc

/-- SAME actual raw row and actual member compiler/opening/instantiation.
The carrier field is generated internally; neither a field value nor any
raw leaf query, quote child code or final equality is supplied. -/
theorem from_head {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z : Fin m)
    (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m)
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral k I))
    (hd : Derives Γ (ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D))
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C Rb S K Hm (P i) r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f u x))
    (hc : Derives Γ (ForcingGuardCode.compiled false R w A f x Q))
    (ho : Derives Γ (substituted w K Hm A f C T Q O))
    (hi : Derives Γ (substituted w r s C T z T O Z)) :
    Derives Γ (.equal (H (memberPosition i)) Z) := by
  have hw := Derives.conjL hf
  have hz := Derives.conjL (Derives.conjR (Derives.conjR hf))
  have hIW := SyntaxNumerals.range hZ k w I hw hI
  have he := StructuralListFieldValues.exists_value hZ w S I hw hIW
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (StructuralListFieldSyntax.field w.castSucc S.castSucc I.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have hA11 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 A1 Fin.castSucc) (under hA1 E)
  have hA21 := of_eq (SyntaxNumeralSyntax.numeral_rename 2 A2 Fin.castSucc) (under hA2 E)
  have hI1 := of_eq (SyntaxNumeralSyntax.numeral_rename k I Fin.castSucc) (under hI E)
  have hd1 := of_eq (ForcingPreorderLeaves.data_rename test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D Fin.castSucc) (under hd E)
  have hf1 := of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C Rb S K Hm (P i) r s Fin.castSucc) (under hf E)
  have hh1 := of_eq (SyntaxMixedImageHead.head_rename w A f u x Fin.castSucc) (under hh E)
  have hc1 := of_eq (ForcingGuardCode.compiled_rename false R w A f x Q Fin.castSucc) (under hc E)
  have ho1 := of_eq (substituted_rename w K Hm A f C T Q O Fin.castSucc) (under ho E)
  have hi1 := of_eq (substituted_rename w r s C T z T O Z Fin.castSucc) (under hi E)
  have hRaw := raw_from_data hZ1 test R i w.castSucc z.castSucc A1.castSucc A2.castSucc A3.castSucc f.castSucc T.castSucc C.castSucc B.castSucc S.castSucc Refl.castSucc Pre.castSucc I.castSucc (Fin.last m)
    (fun j => (v j).castSucc) (fun j => (Gb j).castSucc) (fun j => (H j).castSucc)
    (fun j => (U j).castSucc) (fun j => (F j).castSucc) (fun j => (P j).castSucc) (fun j => (N j).castSucc) (fun j => (D j).castSucc)
    hw1 hz1 hA11 hA21 hI1 hd1 (.conjR hE)
  have hGuard := ForcingMemberGuardOpening.from_head hZ1 R w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc Rb.castSucc S.castSucc K.castSucc Hm.castSucc (P i).castSucc r.castSucc s.castSucc
    I.castSucc (Fin.last m) u.castSucc x.castSucc Q.castSucc O.castSucc Z.castSucc hf1 hI1 hh1 (.conjR hE) hc1 ho1 hi1
  exact same_result hZ1 w.castSucc (P i).castSucc (Fin.last m) (H (memberPosition i)).castSucc Z.castSucc hw1 hRaw hGuard


def input {k m} (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Formula m :=
  (SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral k I).conj ((ForcingPreorderLeaves.data test R w z A1 A2 A3 f T C B S Refl Pre v Gb H U F P N D).conj ((ForcingMemberGuardOpening.frame w mode z a f T A C Rb S K Hm (P i) r s).conj ((SyntaxMixedImageHead.head w A f u x).conj ((ForcingGuardCode.compiled false R w A f x Q).conj ((substituted w K Hm A f C T Q O).conj ((substituted w r s C T z T O Z)))))))))

def sentence {k m} (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) : Source.Sentence :=
  ((input test R i w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z v Gb H U F P N D).imp (.equal (H (memberPosition i)) Z)).close

theorem kernel_certificate {k m} (test : Formula 1) (R : Source.Formula (k+2)) (i : Fin 3)
    (w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z : Fin m) (v : Fin 16 → Fin m) (Gb : Fin 5 → Fin m) (H : Fin 6 → Fin m)
    (U F P : Fin 3 → Fin m) (N : Fin 5 → Fin m) (D : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence test R i w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z v Gb H U F P N D)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input test R i w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z v Gb H U F P N D
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_head (ZFContext.add (ZFContext.source_ZF m) E) test R i w z A1 A2 A3 f T C B S Refl Pre I mode a A Rb K Hm r s u x Q O Z v Gb H U F P N D
    (Derives.conjL (h))
    (Derives.conjL (Derives.conjR (h)))
    (Derives.conjL (Derives.conjR (Derives.conjR (h))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (h)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h))))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h)))))))))


end PPAC.Migration.ForcingPreorderMember
