import PPAC.Migration.ForcingRelationImages
import PPAC.Migration.ForcingPreorderPrefix

/-! SAME raw preorder prefix, native R argument map and bare-R direct table.
Original forest/field and mixed-query proofs are reused. Target scopes and
runtime codes remain arbitrary internal values, including nonstandard. -/
namespace PPAC.Migration.ForcingRelationRawTerms
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field)
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
attribute [local implicit_reducible] YesMetaZFC.SetTheory.signature
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- Exactly the original three-cons order, with no new term values. -/
def reversed {m} (P : Fin 3 → Fin m) : Fin 3 → Fin m :=
  Fin.cases (P 2) (Fin.cases (P 1) (fun _ => P 0))

private theorem reversed_map {m l} (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (reversed P i)) = reversed (fun i => ρ (P i)) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i

/-- Recover the SAME original forest from actual prefixData and the
original typed empty bound table. All heads/tables remain internal values. -/
theorem forest_from_prefix {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f T B0 S : Fin m) (a n q : Fin 4 → Fin m) (P D : Fin 3 → Fin m)
    (hz : Derives Γ (empty z)) (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z T B0))
    (hP : ∀ i, Derives Γ (.mem (P i) w))
    (hd : Derives Γ (ForcingPreorderPrefix.data w z f T B0 S a n q P D)) :
    Derives Γ (SyntaxForestSyntax.forest 3 w (reversed P) (D 2)) := by
  have hLength := Derives.conjR (Derives.conjL (Derives.conjR (Derives.conjR hB0)))
  have hNil := StructuralListLengthConstruct.nil_of_empty_length hZ w B0 z hLength hz
  have hFirst := SyntaxForestSyntax.intro_cons 0 w (fun _ => P 0) (D 0) B0 (hP 0) hNil (Derives.conjL (Derives.conjL hd))
  have hSecond := SyntaxForestSyntax.intro_cons 1 w (Fin.cases (P 1) (fun _ => P 0)) (D 1) (D 0)
    (hP 1) hFirst (Derives.conjL (Derives.conjL (Derives.conjR hd)))
  exact SyntaxForestSyntax.intro_cons 2 w (reversed P) (D 2) (D 1)
    (hP 2) hSecond (Derives.conjL (Derives.conjR (Derives.conjR hd)))

private def indices {m} (z A1 A2 : Fin m) : Fin 3 → Fin m := Fin.cases z (Fin.cases A1 (fun _ => A2))

/-- The finite source profiles belong to the pinned raw quotation only.
The original free image table S and NEW bare-R argument table D are distinct. -/
def frame {k m : Nat} (leaf : Fin 3) (w z A1 A2 f A3 c d S i j M D B F V : Fin m) (P : Fin 3 → Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj
    ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj
      ((NativeSubstitutionSyntax.environment ForcingRelationSource.emptyMap (ForcingRelationSource.atomMap k leaf) w z f A3 f B F).conj
        ((ForcingRelationImages.data k w f c d S (reversed P (ForcingRelationSource.leftIndex leaf))
          (reversed P (ForcingRelationSource.rightIndex leaf)) i j M D).conj (SyntaxForestSyntax.forest 3 w (reversed P) V)))))))

theorem frame_rename {k m l : Nat} (leaf : Fin 3) (w z A1 A2 f A3 c d S i j M D B F V : Fin m) (P : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P).rename ρ =
    frame (k := k) leaf (ρ w) (ρ z) (ρ A1) (ρ A2) (ρ f) (ρ A3) (ρ c) (ρ d) (ρ S) (ρ i) (ρ j) (ρ M) (ρ D) (ρ B) (ρ F) (ρ V) (fun i => ρ (P i)) := by
  simp only [frame, Formula.rename, omega_rename, SyntaxNumeralSyntax.numeral_rename,
    NativeSubstitutionSyntax.environment_rename, ForcingRelationImages.data_rename, SyntaxForestSyntax.forest_rename]
  simp only [← reversed_map]

private theorem at_numeral {m} {Γ : Context m} (p : Fin 3) (z A1 A2 : Fin m)
    (h0 : Derives Γ (SyntaxNumeralSyntax.numeral 0 z)) (h1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1))
    (h2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2)) : Derives Γ (SyntaxNumeralSyntax.numeral p.val (indices z A1 A2 p)) := by
  exact Fin.cases h0 (Fin.cases h1 (Fin.cases h2 (fun i => Fin.elim0 i))) p

private theorem argument_point {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3) (right : Bool)
    (w z A1 A2 f A3 c d S i j M D B F V B0 x u v y : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w (if right then j else i) x))
    (hPath : Derives Γ (ForcingRelationImages.guardPath w z f A3 c d B F V S B0 D x u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have hz := Derives.conjL (Derives.conjR hF)
  have hA1 := Derives.conjL (Derives.conjR (Derives.conjR hF))
  have hA2 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hF)))
  have hf := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))
  have he := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF)))))
  have hD := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))))
  have hV := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))))
  let slotIndex : Fin (k+2) := if right then Fin.last (k+1) else (Fin.last k).castSucc
  let rawIndex : Fin 3 := if right then ForcingRelationSource.rightIndex leaf else ForcingRelationSource.leftIndex leaf
  let J := indices z A1 A2 rawIndex
  let rho : Fin (k+2) → PureSyntaxQuotation.Tm (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context 3) (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_context (k+2)) := ForcingRelationSource.arguments
    (.bvar (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (ForcingRelationSource.leftIndex leaf)))
    (.bvar (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (ForcingRelationSource.rightIndex leaf)))
  have hi : Derives Γ (SyntaxNumeralSyntax.numeral slotIndex.val (if right then j else i)) := by
    cases right
    · exact Derives.conjL hD
    · exact Derives.conjL (Derives.conjR hD)
  have hu := ForcingRelationImages.mapped_variable hZ rho slotIndex w z f A3 f B F (if right then j else i) x u
    hw he hi hx (Derives.conjL hPath)
  have hIndex : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable rawIndex).index = rawIndex.val :=
    ProjectNativeRenaming.variable_index (fun _ : Fin 1 => rawIndex) (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (0 : Fin 1))
  have hQuote : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 0 [PureSyntaxQuotation.Original.leaf rawIndex.val]) w u) := by
    apply of_eq _ hu
    cases right <;> simp only [rho, slotIndex, rawIndex, Bool.false_eq_true, ↓reduceIte, ForcingRelationSource.arguments,
      Fin.lastCases_castSucc, Fin.lastCases_last, PureQuotationSyntax.term, PureSyntaxQuotation.termTree] at *
    · rw [hIndex]
    · rw [hIndex]
  have hJ := at_numeral rawIndex z A1 A2 hz hA1 hA2
  have hU := OriginalQuotationVariableFields.variable_of_tree hZ true rawIndex.val w J u hw hJ hQuote
  have hMidQuery := Derives.conjL (Derives.conjR hPath)
  have hLists1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V S A3 f c d u v hMidQuery)
  have hMid := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ true w V S A3 f c d u v J hw hLists1 hU)) hMidQuery
  have hv := Derives.impE (Derives.conjL (SyntaxForestFieldValues.field_at hZ 3 w (reversed P) V rawIndex J v hw hV hJ)) (Derives.conjR hMid)
  have hDirectQuery := Derives.conjR (Derives.conjR hPath)
  have hLists2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B0 D z f c d x y hDirectQuery)
  have hDir := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B0 D z f c d x y (if right then j else i) hw hLists2 hx)) hDirectQuery
  have hy : Derives Γ (.equal y (reversed P rawIndex)) := by
    cases right
    · exact Derives.impE (Derives.conjL (ForcingRelationImages.left_field hZ k w f c d S _ _ i j M D y hf hD)) (Derives.conjR hDir)
    · exact Derives.impE (Derives.conjL (ForcingRelationImages.right_field hZ k w f c d S _ _ i j M D y hf hD)) (Derives.conjR hDir)
  exact eq_trans hv (eq_symm hy)

private theorem parameter_point {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3) (p : Fin k)
    (w z A1 A2 f A3 c d S i j M D B F V B0 I x u v y : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral p.val I)) (hx : Derives Γ (SyntaxVariableSyntax.code false w I x))
    (hPath : Derives Γ (ForcingRelationImages.guardPath w z f A3 c d B F V S B0 D x u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have hf := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))
  have he := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF)))))
  have hD := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))))
  have hu := ForcingRelationImages.mapped_variable hZ
    (ForcingRelationSource.arguments
      (.bvar (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (ForcingRelationSource.leftIndex leaf)))
      (.bvar (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (ForcingRelationSource.rightIndex leaf))))
    p.castSucc.castSucc w z f A3 f B F I x u hw he hI hx (Derives.conjL hPath)
  have hIndex : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable p.castSucc.castSucc).index = p.val :=
    ProjectNativeRenaming.variable_index (fun _ : Fin 1 => p.castSucc.castSucc) (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (0 : Fin 1))
  have hQuote : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 1 [PureSyntaxQuotation.Original.leaf p.val]) w u) :=
    of_eq (by simp only [ForcingRelationSource.arguments, Fin.lastCases_castSucc, PureQuotationSyntax.term, PureSyntaxQuotation.termTree, hIndex]) hu
  have hU := OriginalQuotationVariableFields.variable_of_tree hZ false p.val w I u hw hI hQuote
  have hMidQuery := Derives.conjL (Derives.conjR hPath)
  have hLists1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V S A3 f c d u v hMidQuery)
  have hMid := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w V S A3 f c d u v I hw hLists1 hU)) hMidQuery
  have hDirectQuery := Derives.conjR (Derives.conjR hPath)
  have hLists2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B0 D z f c d x y hDirectQuery)
  have hDir := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B0 D z f c d x y I hw hLists2 hx)) hDirectQuery
  have hy := Derives.impE (Derives.conjL (ForcingRelationImages.parameter_field hZ k p w f c d S _ _ i j M D I y hf hD hI)) (Derives.conjR hDir)
  exact StructuralListFieldValues.unique hZ w S I v y hw (SyntaxNumerals.range hZ p.val w I hw hI) (Derives.conjR hMid) hy

private theorem index_point {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3) (p : Fin (k+2))
    (w z A1 A2 f A3 c d S i j M D B F V B0 I x u v y : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hI : Derives Γ (SyntaxNumeralSyntax.numeral p.val I)) (hx : Derives Γ (SyntaxVariableSyntax.code false w I x))
    (hPath : Derives Γ (ForcingRelationImages.guardPath w z f A3 c d B F V S B0 D x u v y)) : Derives Γ (.equal v y) := by
  have hD := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))))
  revert hI
  refine Fin.lastCases ?_ (fun q => Fin.lastCases ?_ (fun p => ?_) q) p
  · intro hI
    have hEq := SyntaxNumerals.unique hZ (k+1) I j hI (Derives.conjL (Derives.conjR hD))
    exact argument_point hZ leaf true w z A1 A2 f A3 c d S i j M D B F V B0 x u v y P hF
      (SyntaxVariableImagePoint.code_subst_index false w I x j hEq hx) hPath
  · intro hI
    have hEq := SyntaxNumerals.unique hZ k I i hI (Derives.conjL hD)
    exact argument_point hZ leaf false w z A1 A2 f A3 c d S i j M D B F V B0 x u v y P hF
      (SyntaxVariableImagePoint.code_subst_index false w I x i hEq hx) hPath
  · intro hI
    exact parameter_point hZ leaf p w z A1 A2 f A3 c d S i j M D B F V B0 I x u v y P hF hI hx hPath

/-- Full INTERNAL term comparison. Fixed source R arity/profiles are only
quotation metadata; target c,d and all term/output candidates are internal.
No expected equality, image-field answer or preorder truth is supplied. -/
theorem term {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3)
    (w z A1 A2 f A3 c d S i j M D B F V B0 x u v y : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hPath : Derives Γ (ForcingRelationImages.guardPath w z f A3 c d B F V S B0 D x u v y)) : Derives Γ (.equal v y) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w B F z f A3 f x u (Derives.conjL hPath)
  apply Derives.disjE (Derives.conjR ht)
  · let E := SyntaxTermSyntax.branch true w z x
    let Q := SyntaxTermSyntax.branchWitness true w z x
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w z x _ (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hz := Derives.conjL (Derives.conjR hF)
    have hz1 := of_eq (SyntaxNumeralSyntax.numeral_rename 0 z Fin.castSucc) (under (add hz E) Q)
    exact .botE (.impE (OmegaSyntax.empty_at z.castSucc (Fin.last m) hz1) (Derives.conjL hQ))
  · let E := SyntaxTermSyntax.branch false w f x
    let Q := SyntaxTermSyntax.branchWitness false w f x
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w f x _ (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) Q
    have hF1 := of_eq (frame_rename (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P Fin.castSucc) (under (add hF E) Q)
    have hPath1 := of_eq (ForcingRelationImages.guardPath_rename w z f A3 c d B F V S B0 D x u v y Fin.castSucc) (under (add hPath E) Q)
    have hf1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF1))))
    have hBelow := Derives.impE (Derives.conjL (SyntaxNumeralMembers.member_iff hZ1 (k+2) f.castSucc (Fin.last m) hf1)) (Derives.conjL hQ)
    have hCases := SyntaxPositionSyntax.below_imp (k+2) (Fin.last m) (.equal v.castSucc y.castSucc) (fun p => by
      apply Derives.impI
      exact index_point (ZFContext.add hZ1 _) leaf p w.castSucc z.castSucc A1.castSucc A2.castSucc f.castSucc A3.castSucc c.castSucc d.castSucc
        S.castSucc i.castSucc j.castSucc M.castSucc D.castSucc B.castSucc F.castSucc V.castSucc B0.castSucc (Fin.last m)
        x.castSucc u.castSucc v.castSucc y.castSucc (fun i => (P i).castSucc) (add hF1 _) (.hyp (Or.inl rfl)) (add (Derives.conjR hQ) _) (add hPath1 _))
    exact Derives.impE hCases hBelow

def sentence {k m : Nat} (leaf : Fin 3) (w z A1 A2 f A3 c d S i j M D B F V B0 x u v y : Fin m) (P : Fin 3 → Fin m) : Source.Sentence :=
  (((frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P).conj
    (ForcingRelationImages.guardPath w z f A3 c d B F V S B0 D x u v y)).imp (.equal v y)).close

theorem kernel_certificate {k m : Nat} (leaf : Fin 3) (w z A1 A2 f A3 c d S i j M D B F V B0 x u v y : Fin m) (P : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V B0 x u v y P)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P).conj
    (ForcingRelationImages.guardPath w z f A3 c d B F V S B0 D x u v y)
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact term (ZFContext.add (ZFContext.source_ZF m) E) leaf w z A1 A2 f A3 c d S i j M D B F V B0 x u v y P (.conjL h) (.conjR h)

end PPAC.Migration.ForcingRelationRawTerms
