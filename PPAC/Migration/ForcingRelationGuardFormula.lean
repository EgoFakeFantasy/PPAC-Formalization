import PPAC.Migration.ForcingRelationImages
import PPAC.Migration.ForcingBinderFormula

/-! Full formula cancellation for the ACTUAL original guard route from
SAME bare R source versus the generated argument-table route. The existing
all-internal formula cancellation and identity proofs are reused. No new
formula induction, checker, recursor or forcing truth premise is added. -/
namespace PPAC.Migration.ForcingRelationGuardFormula
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

def path {m} (w z f t c d B F V K B0 D n u v y : Fin m) : Formula m :=
  (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n y))

theorem path_rename {m l} (w z f t c d B F V K B0 D n u v y : Fin m) (ρ : Fin m → Fin l) :
    (path w z f t c d B F V K B0 D n u v y).rename ρ =
    path (ρ w) (ρ z) (ρ f) (ρ t) (ρ c) (ρ d) (ρ B) (ρ F) (ρ V) (ρ K) (ρ B0) (ρ D) (ρ n) (ρ u) (ρ v) (ρ y) := by
  simp only [path, Formula.rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem term_diagram {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 I J IB IF : Fin m)
    (hF : Derives Γ (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF z f z f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four z z t c) (four f f f d) (four IB B V B0) (four IF F K D)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let E := (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 IB) (old 5 IF) (old 5 z) (old 5 f) (old 5 z) (old 5 f) (slot 5 0) (slot 5 1)).conj
    ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 B) (old 5 F) (old 5 z) (old 5 f) (old 5 t) (old 5 f) (slot 5 1) (slot 5 2)).conj
      ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 V) (old 5 K) (old 5 t) (old 5 f) (old 5 c) (old 5 d) (slot 5 2) (slot 5 3)).conj
        (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 B0) (old 5 D) (old 5 z) (old 5 f) (old 5 c) (old 5 d) (slot 5 0) (slot 5 4))))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ E
  have hF5 := of_eq (ForcingRelationImages.guardFrame_rename (k := k) w z f t c d S L R i j M D B F V K (old 5)) (HornBinderRules.under_body 5 hF E)
  have hI5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z I (old 5)) (HornBinderRules.under_body 5 hI E)
  have hJ5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 5)) (HornBinderRules.under_body 5 hJ E)
  have he5 := of_eq (IndexTermImageCodeSyntax.environment_rename w I J IB IF z f z f (old 5)) (HornBinderRules.under_body 5 he E)
  have hEq := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 z) (old 5 f) (old 5 I) (old 5 J) (old 5 IB) (old 5 IF)
    (slot 5 0) (slot 5 1) (Derives.conjL hF5) hI5 hJ5 he5 (Derives.conjL hE)
  have hNative := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 B) (old 5 F) (old 5 z) (old 5 f) (old 5 t) (old 5 f)
    (slot 5 1) (slot 5 2) (slot 5 0) (eq_symm hEq) (Derives.conjL (Derives.conjR hE))
  exact ForcingRelationImages.guard_term hZ5 (old 5 w) (old 5 z) (old 5 f) (old 5 t) (old 5 c) (old 5 d)
    (old 5 S) (old 5 L) (old 5 R) (old 5 i) (old 5 j) (old 5 M) (old 5 D) (old 5 B) (old 5 F) (old 5 V) (old 5 K)
    (old 5 B0) (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4) hF5
    (.conjI hNative (.conjI (Derives.conjL (Derives.conjR (Derives.conjR hE))) (Derives.conjR (Derives.conjR (Derives.conjR hE)))))

private theorem at_identity {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 I J IB IF n u v y : Fin m)
    (hF : Derives Γ (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF z f z f))
    (hP : Derives Γ (path w z f t c d B F V K B0 D n u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have h0 := Derives.conjL hP
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B F z f t f n u hw h0
  have hi := SyntaxIdentityInduction.reflexive hZ w I J z f n hw hI hJ ht
  have hId := Derives.impE (Derives.conjL (IndexFormulaRenameBridge.rename_iff hZ w I J IB IF z f z f n n hw he)) hi
  have hd := term_diagram hZ w z f t c d S L R i j M D B F V K B0 I J IB IF hF hI hJ he
  exact ForcingFormulaInduction.cancel hZ w (four z z t c) (four f f f d) (four IB B V B0) (four IF F K D)
    n n u v y hw hd hId h0 (Derives.conjL (Derives.conjR hP)) (Derives.conjR (Derives.conjR hP))

private theorem at_codes {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 I J n u v y : Fin m)
    (hF : Derives Γ (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (hP : Derives Γ (path w z f t c d B F V K B0 D n u v y)) : Derives Γ (.equal v y) := by
  have he := IndexTermImageEnvironment.exists_environment hZ w I J z f z f (Derives.conjL hF)
    (SyntaxIdentityCode.map_code w z I hI) (SyntaxIdentityCode.map_code w f J hJ)
  let E := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (old 2 z) (old 2 f) (old 2 z) (old 2 f)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hF2 := of_eq (ForcingRelationImages.guardFrame_rename (k := k) w z f t c d S L R i j M D B F V K (old 2)) (HornBinderRules.under_body 2 hF E)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z I (old 2)) (HornBinderRules.under_body 2 hI E)
  have hJ2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 2)) (HornBinderRules.under_body 2 hJ E)
  have hP2 := of_eq (path_rename w z f t c d B F V K B0 D n u v y (old 2)) (HornBinderRules.under_body 2 hP E)
  exact at_identity hZ2 (old 2 w) (old 2 z) (old 2 f) (old 2 t) (old 2 c) (old 2 d) (old 2 S) (old 2 L) (old 2 R)
    (old 2 i) (old 2 j) (old 2 M) (old 2 D) (old 2 B) (old 2 F) (old 2 V) (old 2 K) (old 2 B0) (old 2 I) (old 2 J)
    (slot 2 0) (slot 2 1) (old 2 n) (old 2 u) (old 2 v) (old 2 y) hF2 hI2 hJ2 hE hP2

/-- ALL internal formulas, including nonstandard codes, with arbitrary
internal target scopes c,d. Four auxiliary identity codes/tables are
object-generated and eliminated. Existing full formula induction is used
unchanged; no formula output or guard truth is supplied as an answer. -/
theorem formula {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 n u v y : Fin m)
    (hF : Derives Γ (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hP : Derives Γ (path w z f t c d B F V K B0 D n u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have hz := Derives.conjL (Derives.conjR hF)
  have hzW := SyntaxNumerals.range hZ 0 w z hw hz
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc z.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxIdentityCode.exists_code hZ w z hw hzW)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hF1 := of_eq (ForcingRelationImages.guardFrame_rename (k := k) w z f t c d S L R i j M D B F V K Fin.castSucc) (under hF E)
  have hP1 := of_eq (path_rename w z f t c d B F V K B0 D n u v y Fin.castSucc) (under hP E)
  have hw1 := Derives.conjL hF1
  have hf1 := Derives.conjL (Derives.conjR (Derives.conjR hF1))
  have hfW := SyntaxNumerals.range hZ1 (k+2) w.castSucc f.castSucc hw1 hf1
  let Q := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) (SyntaxIdentityCode.exists_code hZ1 w.castSucc f.castSucc hw1 hfW)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Q
  have hF2 := of_eq (ForcingRelationImages.guardFrame_rename (k := k) w.castSucc z.castSucc f.castSucc t.castSucc c.castSucc d.castSucc S.castSucc L.castSucc R.castSucc i.castSucc j.castSucc M.castSucc D.castSucc B.castSucc F.castSucc V.castSucc K.castSucc Fin.castSucc) (under hF1 Q)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc z.castSucc (Fin.last m) Fin.castSucc) (under hE Q)
  have hP2 := of_eq (path_rename w.castSucc z.castSucc f.castSucc t.castSucc c.castSucc d.castSucc B.castSucc F.castSucc V.castSucc K.castSucc B0.castSucc D.castSucc n.castSucc u.castSucc v.castSucc y.castSucc Fin.castSucc) (under hP1 Q)
  exact at_codes hZ2 w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc t.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc
    S.castSucc.castSucc L.castSucc.castSucc R.castSucc.castSucc i.castSucc.castSucc j.castSucc.castSucc M.castSucc.castSucc D.castSucc.castSucc
    B.castSucc.castSucc F.castSucc.castSucc V.castSucc.castSucc K.castSucc.castSucc B0.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    n.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc y.castSucc.castSucc hF2 hI2 hQ hP2

def sentence {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v y : Fin m) : Source.Sentence :=
  (((ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj
    (path w z f t c d B F V K B0 D n u v y)).imp (.equal v y)).close

theorem kernel_certificate {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence (k := k) w z f t c d S L R i j M D B F V K B0 n u v y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj (path w z f t c d B F V K B0 D n u v y)
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact formula (ZFContext.add (ZFContext.source_ZF m) E) w z f t c d S L R i j M D B F V K B0 n u v y (.conjL h) (.conjR h)

/-- Consume the SAME source R quotation/native guard map/query generated
by ForcingRelationSource. No independent native query or output is supplied;
the original raw relation query in that source record is retained. -/
theorem from_source {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (leaf : Fin 3)
    (w z t A f N G X c d S P Q i j M D V K B0 v y : Fin m) (E : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hSource : Derives Γ (ForcingRelationSource.data R leaf w z t A f N G X E))
    (hd : Derives Γ (ForcingRelationImages.data n w f c d S P Q i j M D))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Derives Γ (ForcingReflexiveImages.replacement w f c d S j Q K))
    (hGuard : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d G v))
    (hCommon : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d X y)) : Derives Γ (.equal v y) := by
  have he := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hNative := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hF : Derives Γ (ForcingRelationImages.guardFrame (k := n) w z f t c d S P Q i j M D (E 2) (E 3) V K) :=
    .conjI hw (.conjI hz (.conjI hf (.conjI he (.conjI hd (.conjI hV hK)))))
  exact formula hZ w z f t c d S P Q i j M D (E 2) (E 3) V K B0 X G v y hF (.conjI hNative (.conjI hGuard hCommon))

/-- Generate the common direct query INTERNALLY and rewrite its output
to the SAME actual guard output. No common query/output is an input. -/
theorem to_direct {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 n u v : Fin m)
    (hF : Derives Γ (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z c d B0))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v) := by
  have hw := Derives.conjL hF
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B F z f t f n u hw h0
  have hData := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hF))))
  have hD := ForcingRelationImages.target_type k w f c d S L R i j M D hData
  have hex := SyntaxMixedFormulaOutputInduction.actual_exists hZ w B0 D z f c d n hw (.conjI ht (.conjI hB0 hD))
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc B0.castSucc D.castSucc z.castSucc f.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hex
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hF1 := of_eq (ForcingRelationImages.guardFrame_rename (k := k) w z f t c d S L R i j M D B F V K Fin.castSucc) (under hF E)
  have h01 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B F z f t f n u Fin.castSucc) (under h0 E)
  have h11 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V K t f c d u v Fin.castSucc) (under h1 E)
  have hEq := formula hZ1 w.castSucc z.castSucc f.castSucc t.castSucc c.castSucc d.castSucc S.castSucc L.castSucc R.castSucc
    i.castSucc j.castSucc M.castSucc D.castSucc B.castSucc F.castSucc V.castSucc K.castSucc B0.castSucc n.castSucc u.castSucc v.castSucc (Fin.last m)
    hF1 (.conjI h01 (.conjI h11 hE))
  have hout := SyntaxMixedFormulaJudgmentSubst.subst_q w.castSucc B0.castSucc D.castSucc z.castSucc f.castSucc c.castSucc d.castSucc
    n.castSucc (Fin.last m) v.castSucc (eq_symm hEq) hE
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B0 D z f c d n v Fin.castSucc).symm hout

/-- Actual common-source consumer, with no supplied common-query answer. -/
theorem from_source_to_direct {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (leaf : Fin 3)
    (w z t A f N G X c d S P Q i j M D V K B0 v : Fin m) (E : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hSource : Derives Γ (ForcingRelationSource.data R leaf w z t A f N G X E))
    (hd : Derives Γ (ForcingRelationImages.data n w f c d S P Q i j M D))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Derives Γ (ForcingReflexiveImages.replacement w f c d S j Q K))
    (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z c d B0))
    (hGuard : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d G v)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d X v) := by
  have he := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hNative := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hF : Derives Γ (ForcingRelationImages.guardFrame (k := n) w z f t c d S P Q i j M D (E 2) (E 3) V K) :=
    .conjI hw (.conjI hz (.conjI hf (.conjI he (.conjI hd (.conjI hV hK)))))
  exact to_direct hZ w z f t c d S P Q i j M D (E 2) (E 3) V K B0 X G v hF hB0 hNative hGuard

def directInput {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v : Fin m) : Formula m :=
  (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj
    ((SyntaxMixedImageCodeSyntax.termList w z c d B0).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v)))

def directSentence {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v : Fin m) : Source.Sentence :=
  ((directInput (k := k) w z f t c d S L R i j M D B F V K B0 n u v).imp
    (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v)).close

theorem direct_kernel_certificate {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (directSentence (k := k) w z f t c d S L R i j M D B F V K B0 n u v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := directInput (k := k) w z f t c d S L R i j M D B F V K B0 n u v
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact to_direct (ZFContext.add (ZFContext.source_ZF m) E) w z f t c d S L R i j M D B F V K B0 n u v
    (Derives.conjL h) (Derives.conjL (Derives.conjR h))
    (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjR (Derives.conjR (Derives.conjR h)))

end PPAC.Migration.ForcingRelationGuardFormula
