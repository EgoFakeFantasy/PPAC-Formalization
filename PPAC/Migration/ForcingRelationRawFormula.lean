import PPAC.Migration.ForcingRelationRawTerms
import PPAC.Migration.ForcingRelationGuardFormula

/-! The second ACTUAL path from SAME bare R: original raw relation map,
original three-prefix table, SAME source R record, internally generated
common query to SAME actual raw leaf output. Existing full cancellation,
identity witnesses and mixed-output existence are reused unchanged. -/
namespace PPAC.Migration.ForcingRelationRawFormula
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ForcingRelationGuardFormula (path path_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem term_diagram {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3)
    (w z A1 A2 f A3 c d S i j M D B F V B0 I J IB IF : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I)) (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF z f z f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four z z A3 c) (four f f f d) (four IB B V B0) (four IF F S D)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let E := (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 IB) (old 5 IF) (old 5 z) (old 5 f) (old 5 z) (old 5 f) (slot 5 0) (slot 5 1)).conj
    ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 B) (old 5 F) (old 5 z) (old 5 f) (old 5 A3) (old 5 f) (slot 5 1) (slot 5 2)).conj
      ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 V) (old 5 S) (old 5 A3) (old 5 f) (old 5 c) (old 5 d) (slot 5 2) (slot 5 3)).conj
        (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 B0) (old 5 D) (old 5 z) (old 5 f) (old 5 c) (old 5 d) (slot 5 0) (slot 5 4))))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ E
  have hF5 := of_eq (ForcingRelationRawTerms.frame_rename (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P (old 5)) (HornBinderRules.under_body 5 hF E)
  have hI5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z I (old 5)) (HornBinderRules.under_body 5 hI E)
  have hJ5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 5)) (HornBinderRules.under_body 5 hJ E)
  have he5 := of_eq (IndexTermImageCodeSyntax.environment_rename w I J IB IF z f z f (old 5)) (HornBinderRules.under_body 5 he E)
  have hEq := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 z) (old 5 f) (old 5 I) (old 5 J) (old 5 IB) (old 5 IF)
    (slot 5 0) (slot 5 1) (Derives.conjL hF5) hI5 hJ5 he5 (Derives.conjL hE)
  have hNative := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 B) (old 5 F) (old 5 z) (old 5 f) (old 5 A3) (old 5 f)
    (slot 5 1) (slot 5 2) (slot 5 0) (eq_symm hEq) (Derives.conjL (Derives.conjR hE))
  exact ForcingRelationRawTerms.term hZ5 leaf (old 5 w) (old 5 z) (old 5 A1) (old 5 A2) (old 5 f) (old 5 A3)
    (old 5 c) (old 5 d) (old 5 S) (old 5 i) (old 5 j) (old 5 M) (old 5 D) (old 5 B) (old 5 F) (old 5 V) (old 5 B0)
    (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (P i)) hF5
    (.conjI hNative (.conjI (Derives.conjL (Derives.conjR (Derives.conjR hE))) (Derives.conjR (Derives.conjR (Derives.conjR hE)))))

private theorem at_identity {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3)
    (w z A1 A2 f A3 c d S i j M D B F V B0 I J IB IF n u v y : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I)) (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF z f z f))
    (hP : Derives Γ (path w z f A3 c d B F V S B0 D n u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have h0 := Derives.conjL hP
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B F z f A3 f n u hw h0
  have hi := SyntaxIdentityInduction.reflexive hZ w I J z f n hw hI hJ ht
  have hId := Derives.impE (Derives.conjL (IndexFormulaRenameBridge.rename_iff hZ w I J IB IF z f z f n n hw he)) hi
  have hd := term_diagram hZ leaf w z A1 A2 f A3 c d S i j M D B F V B0 I J IB IF P hF hI hJ he
  exact ForcingFormulaInduction.cancel hZ w (four z z A3 c) (four f f f d) (four IB B V B0) (four IF F S D)
    n n u v y hw hd hId h0 (Derives.conjL (Derives.conjR hP)) (Derives.conjR (Derives.conjR hP))

private theorem at_codes {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3)
    (w z A1 A2 f A3 c d S i j M D B F V B0 I J n u v y : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I)) (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (hP : Derives Γ (path w z f A3 c d B F V S B0 D n u v y)) : Derives Γ (.equal v y) := by
  have he := IndexTermImageEnvironment.exists_environment hZ w I J z f z f (Derives.conjL hF)
    (SyntaxIdentityCode.map_code w z I hI) (SyntaxIdentityCode.map_code w f J hJ)
  let E := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (old 2 z) (old 2 f) (old 2 z) (old 2 f)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hF2 := of_eq (ForcingRelationRawTerms.frame_rename (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P (old 2)) (HornBinderRules.under_body 2 hF E)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z I (old 2)) (HornBinderRules.under_body 2 hI E)
  have hJ2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 2)) (HornBinderRules.under_body 2 hJ E)
  have hP2 := of_eq (path_rename w z f A3 c d B F V S B0 D n u v y (old 2)) (HornBinderRules.under_body 2 hP E)
  exact at_identity hZ2 leaf (old 2 w) (old 2 z) (old 2 A1) (old 2 A2) (old 2 f) (old 2 A3) (old 2 c) (old 2 d) (old 2 S)
    (old 2 i) (old 2 j) (old 2 M) (old 2 D) (old 2 B) (old 2 F) (old 2 V) (old 2 B0) (old 2 I) (old 2 J)
    (slot 2 0) (slot 2 1) (old 2 n) (old 2 u) (old 2 v) (old 2 y) (fun i => old 2 (P i)) hF2 hI2 hJ2 hE hP2

/-- ALL internal formulas. Four identity code/image witnesses are generated
and eliminated in ZF; original full formula induction is reused unchanged. -/
theorem formula {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3)
    (w z A1 A2 f A3 c d S i j M D B F V B0 n u v y : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hP : Derives Γ (path w z f A3 c d B F V S B0 D n u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have hz := Derives.conjL (Derives.conjR hF)
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxIdentityCode.exists_code hZ w z hw (SyntaxNumerals.range hZ 0 w z hw hz))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hF1 := of_eq (ForcingRelationRawTerms.frame_rename (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P Fin.castSucc) (under hF E)
  have hP1 := of_eq (path_rename w z f A3 c d B F V S B0 D n u v y Fin.castSucc) (under hP E)
  have hw1 := Derives.conjL hF1
  have hf1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF1))))
  let Q := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) (SyntaxIdentityCode.exists_code hZ1 w.castSucc f.castSucc hw1 (SyntaxNumerals.range hZ1 (k+2) w.castSucc f.castSucc hw1 hf1))
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Q
  have hF2 := of_eq (ForcingRelationRawTerms.frame_rename (k := k) leaf w.castSucc z.castSucc A1.castSucc A2.castSucc f.castSucc A3.castSucc c.castSucc d.castSucc S.castSucc i.castSucc j.castSucc M.castSucc D.castSucc B.castSucc F.castSucc V.castSucc (fun i => (P i).castSucc) Fin.castSucc) (under hF1 Q)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc z.castSucc (Fin.last m) Fin.castSucc) (under hE Q)
  have hP2 := of_eq (path_rename w.castSucc z.castSucc f.castSucc A3.castSucc c.castSucc d.castSucc B.castSucc F.castSucc V.castSucc S.castSucc B0.castSucc D.castSucc n.castSucc u.castSucc v.castSucc y.castSucc Fin.castSucc) (under hP1 Q)
  exact at_codes hZ2 leaf w.castSucc.castSucc z.castSucc.castSucc A1.castSucc.castSucc A2.castSucc.castSucc f.castSucc.castSucc A3.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
    S.castSucc.castSucc i.castSucc.castSucc j.castSucc.castSucc M.castSucc.castSucc D.castSucc.castSucc B.castSucc.castSucc F.castSucc.castSucc V.castSucc.castSucc B0.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc y.castSucc.castSucc (fun i => (P i).castSucc.castSucc) hF2 hI2 hQ hP2

/-- INTERNALLY generate the common direct query and rewrite its output to
SAME actual raw relation leaf output; no common-query/output answer is input. -/
theorem to_direct {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (leaf : Fin 3)
    (w z A1 A2 f A3 c d S i j M D B F V B0 n u v : Fin m) (P : Fin 3 → Fin m)
    (hF : Derives Γ (ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P))
    (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z c d B0))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f A3 f n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V S A3 f c d u v)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v) := by
  have hw := Derives.conjL hF
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B F z f A3 f n u hw h0
  have hData := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))))
  have hD := ForcingRelationImages.target_type k w f c d S _ _ i j M D hData
  have hex := SyntaxMixedFormulaOutputInduction.actual_exists hZ w B0 D z f c d n hw (.conjI ht (.conjI hB0 hD))
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc B0.castSucc D.castSucc z.castSucc f.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hF1 := of_eq (ForcingRelationRawTerms.frame_rename (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P Fin.castSucc) (under hF E)
  have h01 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B F z f A3 f n u Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V S A3 f c d u v Fin.castSucc) (under h1 E)
  have hEq := formula hZ1 leaf w.castSucc z.castSucc A1.castSucc A2.castSucc f.castSucc A3.castSucc c.castSucc d.castSucc S.castSucc
    i.castSucc j.castSucc M.castSucc D.castSucc B.castSucc F.castSucc V.castSucc B0.castSucc n.castSucc u.castSucc v.castSucc (Fin.last m) (fun i => (P i).castSucc)
    hF1 (.conjI h01 (.conjI h11 hE))
  have hout := SyntaxMixedFormulaJudgmentSubst.subst_q w.castSucc B0.castSucc D.castSucc z.castSucc f.castSucc c.castSucc d.castSucc
    n.castSucc (Fin.last m) v.castSucc (eq_symm hEq) hE
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B0 D z f c d n v Fin.castSucc).symm hout

/-- Actual original prefix/source-record consumer. Recover SAME final
forest from actual prefixData; consume SAME native raw relation query and
actual leaf query. No forest, common query or output identity is supplied. -/
theorem from_prefix {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (leaf : Fin 3)
    (w z A1 A2 A3 g f T R0 S N G X i j M D v : Fin m) (E a n q : Fin 4 → Fin m) (P V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hSource : Derives Γ (ForcingRelationSource.data R leaf w z g A3 f N G X E))
    (hPrefix : Derives Γ (ForcingPreorderPrefix.data w z f T R0 S a n q P V))
    (hR0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z T R0))
    (hP : ∀ i, Derives Γ (.mem (P i) w))
    (hImages : Derives Γ (ForcingRelationImages.data k w f z T S (ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf))
      (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf)) i j M D))
    (hLeaf : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (V 2) S A3 f z T N v)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R0 D z f z T X v) := by
  have hForest := ForcingRelationRawTerms.forest_from_prefix hZ w z f T R0 S a n q P V hz hR0 hP hPrefix
  have he := Derives.conjL (Derives.conjR hSource)
  have hNative := Derives.conjL (Derives.conjR (Derives.conjR hSource))
  have hF : Derives Γ (ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 z T S i j M D (E 0) (E 1) (V 2) P) :=
    .conjI hw (.conjI hz (.conjI hA1 (.conjI hA2 (.conjI hf (.conjI he (.conjI hImages hForest))))))
  exact to_direct hZ leaf w z A1 A2 f A3 z T S i j M D (E 0) (E 1) (V 2) R0 X N v P hF hR0 hNative hLeaf

def sentence {k m : Nat} (leaf : Fin 3) (w z A1 A2 f A3 c d S i j M D B F V B0 n u v : Fin m) (P : Fin 3 → Fin m) : Source.Sentence :=
  (((ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P).conj
    ((SyntaxMixedImageCodeSyntax.termList w z c d B0).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f A3 f n u).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w V S A3 f c d u v)))).imp
    (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v)).close

theorem kernel_certificate {k m : Nat} (leaf : Fin 3) (w z A1 A2 f A3 c d S i j M D B F V B0 n u v : Fin m) (P : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V B0 n u v P)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (ForcingRelationRawTerms.frame (k := k) leaf w z A1 A2 f A3 c d S i j M D B F V P).conj
    ((SyntaxMixedImageCodeSyntax.termList w z c d B0).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f A3 f n u).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w V S A3 f c d u v)))
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact to_direct (ZFContext.add (ZFContext.source_ZF m) E) leaf w z A1 A2 f A3 c d S i j M D B F V B0 n u v P
    (Derives.conjL h) (Derives.conjL (Derives.conjR h)) (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjR (Derives.conjR (Derives.conjR h)))

/-- Identify the SAME actual raw relation leaf and actual guard output.
Both common queries are generated internally from SAME R data and SAME D;
no desired equality, common query/output or guard truth is assumed. -/
theorem relation_leaf {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (leaf : Fin 3)
    (w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg : Fin m)
    (E a n q : Fin 4 → Fin m) (P V : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hA1 : Derives Γ (SyntaxNumeralSyntax.numeral 1 A1)) (hA2 : Derives Γ (SyntaxNumeralSyntax.numeral 2 A2))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f))
    (hSource : Derives Γ (ForcingRelationSource.data R leaf w z g A3 f N G X E))
    (hPrefix : Derives Γ (ForcingPreorderPrefix.data w z f T R0 S a n q P V))
    (hR0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z z T R0))
    (hP : ∀ i, Derives Γ (.mem (P i) w))
    (hImages : Derives Γ (ForcingRelationImages.data k w f z T S (ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf))
      (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf)) i j M D))
    (hVg : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf)) Vg))
    (hK : Derives Γ (ForcingReflexiveImages.replacement w f z T S j (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf)) K))
    (hRaw : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (V 2) S A3 f z T N vr))
    (hGuard : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w Vg K g f z T G vg)) : Derives Γ (.equal vr vg) := by
  have hCommonRaw := from_prefix hZ R leaf w z A1 A2 A3 g f T R0 S N G X i j M D vr E a n q P V
    hw hz hA1 hA2 hf hSource hPrefix hR0 hP hImages hRaw
  have hCommonGuard := ForcingRelationGuardFormula.from_source_to_direct hZ R leaf w z g A3 f N G X z T S
    (ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf)) (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf))
    i j M D Vg K R0 vg E hw hz hf hSource hImages hVg hK hR0 hGuard
  exact SyntaxMixedFormulaOutputInduction.unique hZ w R0 D z f z T X vr vg hw hCommonRaw hCommonGuard

def leafInput {k m} (R : Source.Formula (k+2)) (leaf : Fin 3) (w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg : Fin m)
    (E a n q : Fin 4 → Fin m) (P V : Fin 3 → Fin m) : Formula m :=
  (omega w).conj ((SyntaxNumeralSyntax.numeral 0 z).conj ((SyntaxNumeralSyntax.numeral 1 A1).conj ((SyntaxNumeralSyntax.numeral 2 A2).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((ForcingRelationSource.data R leaf w z g A3 f N G X E).conj ((ForcingPreorderPrefix.data w z f T R0 S a n q P V).conj ((SyntaxMixedImageCodeSyntax.termList w z z T R0).conj (((Formula.mem (P 0) w).conj ((Formula.mem (P 1) w).conj (.mem (P 2) w))).conj ((ForcingRelationImages.data k w f z T S (ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf)) (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf)) i j M D).conj ((SyntaxForestSyntax.forest 1 w (fun _ => ForcingRelationRawTerms.reversed P (ForcingRelationSource.leftIndex leaf)) Vg).conj ((ForcingReflexiveImages.replacement w f z T S j (ForcingRelationRawTerms.reversed P (ForcingRelationSource.rightIndex leaf)) K).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w (V 2) S A3 f z T N vr).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w Vg K g f z T G vg))))))))))))))

def leafSentence {k m} (R : Source.Formula (k+2)) (leaf : Fin 3) (w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg : Fin m)
    (E a n q : Fin 4 → Fin m) (P V : Fin 3 → Fin m) : Source.Sentence :=
  ((leafInput R leaf w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg E a n q P V).imp (.equal vr vg)).close

theorem leaf_kernel_certificate {k m} (R : Source.Formula (k+2)) (leaf : Fin 3) (w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg : Fin m)
    (E a n q : Fin 4 → Fin m) (P V : Fin 3 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (leafSentence R leaf w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg E a n q P V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let H := leafInput R leaf w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg E a n q P V
  let Γ := Context.add H (Source.SetLanguage.ZF.at m)
  have h : Derives Γ H := .hyp (Or.inl rfl)
  have hPNat := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))))
  have hP : ∀ i : Fin 3, Derives Γ (.mem (P i) w) := by
    intro i
    exact Fin.cases (Derives.conjL hPNat) (Fin.cases (Derives.conjL (Derives.conjR hPNat)) (Fin.cases (Derives.conjR (Derives.conjR hPNat)) (fun i => Fin.elim0 i))) i
  exact relation_leaf (ZFContext.add (ZFContext.source_ZF m) H) R leaf w z A1 A2 A3 g f T R0 S N G X i j M D Vg K vr vg E a n q P V
    (Derives.conjL h) (Derives.conjL (Derives.conjR h)) (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h)))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))) hP (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))))))))) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))))))))

end PPAC.Migration.ForcingRelationRawFormula
