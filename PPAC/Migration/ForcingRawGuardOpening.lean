import PPAC.Migration.ForcingFreshParentOpening
import PPAC.Migration.ForcingGuardOpening
import PPAC.Migration.ForcingRelationGuardFormula
import PPAC.Migration.ForcingWeakenedOverwrite

/-! The real guard compiler followed by ONE actual raw-body substitution.
Its bound table is the actual fresh cons table; its free table may already
contain condition overwrites. Do not require the unrelated fixed OpenLayout.
Reuse original singleton/identity fields and full FormulaInduction.cancel. -/
namespace PPAC.Migration.ForcingRawGuardOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxCodedMixedTermSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def frame {m} (w z t A f T head B I D S P V : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxNumeralSyntax.numeral 1 t).conj
    ((SyntaxVariableSyntax.code true w z head).conj
      ((SyntaxForestSyntax.forest 1 w (fun _ => head) B).conj
        ((ForcingAtomicCode.identityImages w A f I).conj
          ((SyntaxMixedImageCodeSyntax.termLists w A f z T D S).conj
            ((StructuralListFieldSyntax.field w D z P).conj
              (SyntaxForestSyntax.forest 1 w (fun _ => P) V))))))))

theorem frame_rename {m l} (w z t A f T head B I D S P V : Fin m) (rho : Fin m → Fin l) :
    (frame w z t A f T head B I D S P V).rename rho =
      frame (rho w) (rho z) (rho t) (rho A) (rho f) (rho T) (rho head)
        (rho B) (rho I) (rho D) (rho S) (rho P) (rho V) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, SyntaxNumeralSyntax.numeral_rename,
    SyntaxVariableSyntax.code_rename, SyntaxForestSyntax.forest_rename, ForcingAtomicCode.identityImages_rename,
    SyntaxMixedImageCodeSyntax.termLists_rename, StructuralListFieldSyntax.field_rename]

def path {m} (w t A f z T B I D S V x u y o : Fin m) : Formula m :=
  (substituted w B I t f A f x u).conj
    ((substituted w D S A f z T u y).conj (substituted w V S t f z T x o))

theorem path_rename {m l} (w t A f z T B I D S V x u y o : Fin m) (rho : Fin m → Fin l) :
    (path w t A f z T B I D S V x u y o).rename rho =
      path (rho w) (rho t) (rho A) (rho f) (rho z) (rho T) (rho B) (rho I)
        (rho D) (rho S) (rho V) (rho x) (rho u) (rho y) (rho o) := by
  simp only [path, Formula.rename, substituted_rename]

private structure Inputs {m} (Gamma : Context m) (w z t A f T head B I D S P V x u y o : Fin m) : Prop where
  zf : ZFContext.Evidence Gamma
  hf : Derives Gamma (frame w z t A f T head B I D S P V)
  hp : Derives Gamma (path w t A f z T B I D S V x u y o)

private theorem Inputs.in_body {m l} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) (E : Formula (m+l)) :
    Inputs (Context.add E (raisedContext l Gamma)) (old l w) (old l z) (old l t) (old l A) (old l f)
      (old l T) (old l head) (old l B) (old l I) (old l D) (old l S) (old l P) (old l V)
      (old l x) (old l u) (old l y) (old l o) :=
  ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (frame_rename w z t A f T head B I D S P V (old l)) (HornBinderRules.under_body l h.hf E),
    of_eq (path_rename w t A f z T B I D S V x u y o (old l)) (HornBinderRules.under_body l h.hp E)⟩

private theorem Inputs.hw {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (omega w) := .conjL h.hf
private theorem Inputs.hz {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (empty z) := .conjL (.conjR h.hf)
private theorem Inputs.ht {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (SyntaxNumeralSyntax.numeral 1 t) :=
  .conjL (.conjR (.conjR h.hf))
private theorem Inputs.head {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (SyntaxVariableSyntax.code true w z head) :=
  .conjL (.conjR (.conjR (.conjR h.hf)))
private theorem Inputs.bound {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (SyntaxForestSyntax.forest 1 w (fun _ => head) B) :=
  .conjL (.conjR (.conjR (.conjR (.conjR h.hf))))
private theorem Inputs.identity {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (ForcingAtomicCode.identityImages w A f I) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))
private theorem Inputs.lists {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (SyntaxMixedImageCodeSyntax.termLists w A f z T D S) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.hf))))))
private theorem Inputs.zero {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (StructuralListFieldSyntax.field w D z P) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))))
private theorem Inputs.direct {m} {Gamma : Context m} {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) : Derives Gamma (SyntaxForestSyntax.forest 1 w (fun _ => P) V) :=
  .conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))))

private theorem variable_point {m} {Gamma : Context m} (bound : Bool)
    {w z t A f T head B I D S P V x u y o : Fin m}
    (h : Inputs Gamma w z t A f T head B I D S P V x u y o) (i : Fin m)
    (hi : Derives Gamma (.mem i (SyntaxTermSyntax.limit bound t f)))
    (hc : Derives Gamma (SyntaxVariableSyntax.code bound w i x)) : Derives Gamma (.equal y o) := by
  have first := Derives.conjL h.hp
  have second := Derives.conjL (.conjR h.hp)
  have direct := Derives.conjR (.conjR h.hp)
  have firstLists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B I t f A f x u first)
  have directLists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V S t f z T x o direct)
  cases bound with
  | true =>
    have below := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff h.zf 1 t i h.ht)) hi
    have emptyi := Derives.disjE below (.botE (.hyp (Or.inl rfl))) (.hyp (Or.inl rfl))
    have iz := OmegaUniversal.empty_unique i z (ZFContext.arithmetic h.zf).base.extensionality emptyi h.hz
    have code := SyntaxVariableImagePoint.code_subst_index true w i x z iz hc
    have field0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true
      w B I t f A f x u z h.hw firstLists code)) first
    have uh := Derives.impE (.conjL (SyntaxForestFieldValues.field_at h.zf 1 w (fun _ => head) B 0 z u h.hw h.bound h.hz)) (.conjR field0)
    have second' := SyntaxMixedFormulaAtomicSubst.term_source w D S A f z T u y head uh second
    have field1 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true
      w D S A f z T head y z h.hw h.lists h.head)) second'
    have yz := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic h.zf).base.extensionality h.hw h.hz
    have yp := StructuralListFieldValues.unique h.zf w D z y P h.hw yz (.conjR field1) h.zero
    have field2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true
      w V S t f z T x o z h.hw directLists code)) direct
    have op := Derives.impE (.conjL (SyntaxForestFieldValues.field_at h.zf 1 w (fun _ => P) V 0 z o h.hw h.direct h.hz)) (.conjR field2)
    exact eq_trans yp (eq_symm op)
  | false =>
    have field0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false
      w B I t f A f x u i h.hw firstLists hc)) first
    have cu := ForcingMemberGuard.identity_field h.zf w A f I i u h.identity (.conjL field0) (.conjR field0)
    have field1 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false
      w D S A f z T u y i h.hw h.lists cu)) second
    have field2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false
      w V S t f z T x o i h.hw directLists hc)) direct
    exact StructuralListFieldValues.unique h.zf w S i y o h.hw
      (SyntaxVariableDecode.index_natural false w i x hc) (.conjR field1) (.conjR field2)

/-- ALL internal template terms. Singleton bound scope is eliminated by the
original numeral law; free indices remain arbitrary internal naturals. -/
theorem term {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z t A f T head B I D S P V x u y o : Fin m)
    (hf : Derives Gamma (frame w z t A f T head B I D S P V))
    (hp : Derives Gamma (path w t A f z T B I D S V x u y o)) : Derives Gamma (.equal y o) := by
  have h : Inputs Gamma w z t A f T head B I D S P V x u y o := ⟨hZ,hf,hp⟩
  apply OriginalTermScopeElimination.eliminate w t f x (.equal y o)
    (SyntaxCodedMixedTermTyping.source_type w B I t f A f x u (.conjL hp))
  intro bound
  cases bound
  · let E := SyntaxTermSyntax.branchWitness false w f x
    have hE : Derives (Context.add E (Context.image Formula.raise Gamma)) E := .hyp (Or.inl rfl)
    exact variable_point false (h.in_body E) (Fin.last m) (.conjL hE) (.conjR hE)
  · let E := SyntaxTermSyntax.branchWitness true w t x
    have hE : Derives (Context.add E (Context.image Formula.raise Gamma)) E := .hyp (Or.inl rfl)
    exact variable_point true (h.in_body E) (Fin.last m) (.conjL hE) (.conjR hE)

private def four {alpha : Type} (a b c d : alpha) : Fin 4 → alpha :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

theorem term_diagram {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z t A f T head B I D S P V It Jf R0 S0 : Fin m)
    (hf : Derives Gamma (frame w z t A f T head B I D S P V))
    (hi : Derives Gamma (SyntaxIdentityMapSyntax.identityCode w t It))
    (hj : Derives Gamma (SyntaxIdentityMapSyntax.identityCode w f Jf))
    (he : Derives Gamma (IndexTermImageCodeSyntax.environment w It Jf R0 S0 t f t f)) :
    Derives Gamma (ForcingTermDiagram.diagram w (four t t A z) (four f f f T) (four R0 B D V) (four S0 I S S)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let E := (ForcingTermDiagram.step (old 5 w) (four (old 5 t) (old 5 t) (old 5 A) (old 5 z))
      (four (old 5 f) (old 5 f) (old 5 f) (old 5 T)) (four (old 5 R0) (old 5 B) (old 5 D) (old 5 V))
      (four (old 5 S0) (old 5 I) (old 5 S) (old 5 S)) 0 (slot 5 0) (slot 5 1)).conj
    ((ForcingTermDiagram.step (old 5 w) (four (old 5 t) (old 5 t) (old 5 A) (old 5 z))
      (four (old 5 f) (old 5 f) (old 5 f) (old 5 T)) (four (old 5 R0) (old 5 B) (old 5 D) (old 5 V))
      (four (old 5 S0) (old 5 I) (old 5 S) (old 5 S)) 1 (slot 5 1) (slot 5 2)).conj
      ((ForcingTermDiagram.step (old 5 w) (four (old 5 t) (old 5 t) (old 5 A) (old 5 z))
      (four (old 5 f) (old 5 f) (old 5 f) (old 5 T)) (four (old 5 R0) (old 5 B) (old 5 D) (old 5 V))
      (four (old 5 S0) (old 5 I) (old 5 S) (old 5 S)) 2 (slot 5 2) (slot 5 3)).conj
        (ForcingTermDiagram.step (old 5 w) (four (old 5 t) (old 5 t) (old 5 A) (old 5 z))
      (four (old 5 f) (old 5 f) (old 5 f) (old 5 T)) (four (old 5 R0) (old 5 B) (old 5 D) (old 5 V))
      (four (old 5 S0) (old 5 I) (old 5 S) (old 5 S)) 3 (slot 5 0) (slot 5 4))))
  let Delta := Context.add E (raisedContext 5 Gamma)
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ E
  have hf5 := of_eq (frame_rename w z t A f T head B I D S P V (old 5)) (HornBinderRules.under_body 5 hf E)
  have hw5 := Derives.conjL hf5
  have eq := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 t) (old 5 f)
    (old 5 It) (old 5 Jf) (old 5 R0) (old 5 S0) (slot 5 0) (slot 5 1) hw5
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w t It (old 5)) (HornBinderRules.under_body 5 hi E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f Jf (old 5)) (HornBinderRules.under_body 5 hj E))
    (of_eq (IndexTermImageCodeSyntax.environment_rename w It Jf R0 S0 t f t f (old 5)) (HornBinderRules.under_body 5 he E))
    (.conjL hE)
  have first := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 B) (old 5 I)
    (old 5 t) (old 5 f) (old 5 A) (old 5 f) (slot 5 1) (slot 5 2) (slot 5 0) (eq_symm eq)
    (.conjL (.conjR hE))
  exact term hZ5 (old 5 w) (old 5 z) (old 5 t) (old 5 A) (old 5 f) (old 5 T) (old 5 head)
    (old 5 B) (old 5 I) (old 5 D) (old 5 S) (old 5 P) (old 5 V)
    (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4) hf5
    (.conjI first (.conjI (.conjL (.conjR (.conjR hE))) (.conjR (.conjR (.conjR hE)))))

def formulaPath {m} (w t A f z T B I D S V n q Y O : Fin m) : Formula m :=
  (SyntaxMixedFormulaJudgmentSyntax.substituted w B I t f A f n q).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T q Y).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w V S t f z T n O))

theorem formulaPath_rename {m l} (w t A f z T B I D S V n q Y O : Fin m) (rho : Fin m → Fin l) :
    (formulaPath w t A f z T B I D S V n q Y O).rename rho =
      formulaPath (rho w) (rho t) (rho A) (rho f) (rho z) (rho T) (rho B) (rho I)
        (rho D) (rho S) (rho V) (rho n) (rho q) (rho Y) (rho O) := by
  simp only [formulaPath, Formula.rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem at_identity {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z t A f T head B I D S P V It Jf R0 S0 n q Y O : Fin m)
    (hf : Derives Gamma (frame w z t A f T head B I D S P V))
    (hi : Derives Gamma (SyntaxIdentityMapSyntax.identityCode w t It))
    (hj : Derives Gamma (SyntaxIdentityMapSyntax.identityCode w f Jf))
    (he : Derives Gamma (IndexTermImageCodeSyntax.environment w It Jf R0 S0 t f t f))
    (hp : Derives Gamma (formulaPath w t A f z T B I D S V n q Y O)) : Derives Gamma (.equal Y O) := by
  have hw := Derives.conjL hf
  have h0 := Derives.conjL hp
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B I t f A f n q hw h0
  have hid := SyntaxIdentityInduction.reflexive hZ w It Jf t f n hw hi hj ht
  have hId := Derives.impE (.conjL (IndexFormulaRenameBridge.rename_iff hZ w It Jf R0 S0 t f t f n n hw he)) hid
  exact ForcingFormulaInduction.cancel hZ w (four t t A z) (four f f f T) (four R0 B D V) (four S0 I S S)
    n n q Y O hw (term_diagram hZ w z t A f T head B I D S P V It Jf R0 S0 hf hi hj he)
    hId h0 (.conjL (.conjR hp)) (.conjR (.conjR hp))

private theorem at_codes {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z t A f T head B I D S P V It Jf n q Y O : Fin m)
    (hf : Derives Gamma (frame w z t A f T head B I D S P V))
    (hi : Derives Gamma (SyntaxIdentityMapSyntax.identityCode w t It))
    (hj : Derives Gamma (SyntaxIdentityMapSyntax.identityCode w f Jf))
    (hp : Derives Gamma (formulaPath w t A f z T B I D S V n q Y O)) : Derives Gamma (.equal Y O) := by
  let E := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 It) (old 2 Jf) (slot 2 0) (slot 2 1)
    (old 2 t) (old 2 f) (old 2 t) (old 2 f)
  let Delta := Context.add E (raisedContext 2 Gamma)
  apply HornBinderRules.eliminate_many 2 E _ (IndexTermImageEnvironment.exists_environment hZ w It Jf t f t f (.conjL hf)
    (SyntaxIdentityCode.map_code w t It hi) (SyntaxIdentityCode.map_code w f Jf hj))
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  exact at_identity (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 z) (old 2 t) (old 2 A) (old 2 f) (old 2 T)
    (old 2 head) (old 2 B) (old 2 I) (old 2 D) (old 2 S) (old 2 P) (old 2 V) (old 2 It) (old 2 Jf)
    (slot 2 0) (slot 2 1) (old 2 n) (old 2 q) (old 2 Y) (old 2 O)
    (of_eq (frame_rename w z t A f T head B I D S P V (old 2)) (HornBinderRules.under_body 2 hf E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w t It (old 2)) (HornBinderRules.under_body 2 hi E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f Jf (old 2)) (HornBinderRules.under_body 2 hj E)) hE
    (of_eq (formulaPath_rename w t A f z T B I D S V n q Y O (old 2)) (HornBinderRules.under_body 2 hp E))

/-- ALL internal formulas. The four identity witnesses are internally
generated; the EXISTING complete four-path formula cancellation is called. -/
theorem formula {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z t A f T head B I D S P V n q Y O : Fin m)
    (hf : Derives Gamma (frame w z t A f T head B I D S P V))
    (hp : Derives Gamma (formulaPath w t A f z T B I D S V n q Y O)) : Derives Gamma (.equal Y O) := by
  have hw := Derives.conjL hf
  have tN := SyntaxNumerals.range hZ 1 w t hw (.conjL (.conjR (.conjR hf)))
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc t.castSucc (Fin.last m)
  let Delta := Context.add E (Context.image Formula.raise Gamma)
  apply Derives.exE (p := E) (SyntaxIdentityCode.exists_code hZ w t hw tN)
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hf1 := of_eq (frame_rename w z t A f T head B I D S P V Fin.castSucc) (SourceLogic.under hf E)
  have hp1 := of_eq (formulaPath_rename w t A f z T B I D S V n q Y O Fin.castSucc) (SourceLogic.under hp E)
  have hw1 := Derives.conjL hf1
  have type1 := SyntaxMixedFormulaJudgmentTyping.source_type hZ1 w.castSucc B.castSucc I.castSucc t.castSucc f.castSucc
    A.castSucc f.castSucc n.castSucc q.castSucc hw1 (.conjL hp1)
  have fN := Derives.conjR (.conjR (FormulaCodeProperties.guards w.castSucc n.castSucc t.castSucc f.castSucc type1))
  let F := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Xi := Context.add F (Context.image Formula.raise Delta)
  apply Derives.exE (p := F) (SyntaxIdentityCode.exists_code hZ1 w.castSucc f.castSucc hw1 fN)
  have hF : Derives Xi F := .hyp (Or.inl rfl)
  have out := at_codes (ZFContext.under hZ1 F) w.castSucc.castSucc z.castSucc.castSucc t.castSucc.castSucc
    A.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc head.castSucc.castSucc B.castSucc.castSucc I.castSucc.castSucc
    D.castSucc.castSucc S.castSucc.castSucc P.castSucc.castSucc V.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    n.castSucc.castSucc q.castSucc.castSucc Y.castSucc.castSucc O.castSucc.castSucc
    (of_eq (frame_rename _ _ _ _ _ _ _ _ _ _ _ _ _ Fin.castSucc) (SourceLogic.under hf1 F))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename _ _ _ Fin.castSucc) (SourceLogic.under hE F)) hF
    (of_eq (formulaPath_rename _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fin.castSucc) (SourceLogic.under hp1 F))
  exact out

def sentence {m} (w z t A f T head B I D S P V n q Y O : Fin m) : Source.Sentence :=
  (((frame w z t A f T head B I D S P V).conj (formulaPath w t A f z T B I D S V n q Y O)).imp (.equal Y O)).close

theorem kernel_certificate {m} (w z t A f T head B I D S P V n q Y O : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z t A f T head B I D S P V n q Y O)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact formula (ZFContext.add (ZFContext.source_ZF m) _) w z t A f T head B I D S P V n q Y O
    (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))

private theorem at_bound_map {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (order : Bool) (Reln : Source.Formula (k+2)) (w z A f T D S P head q Y V : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Gamma (omega w)) (hz : Derives Gamma (empty z))
    (hh : Derives Gamma (SyntaxVariableSyntax.code true w z head))
    (hp : Derives Gamma (SyntaxTermSyntax.term w z T P))
    (hl : Derives Gamma (SyntaxMixedImageCodeSyntax.termLists w A f z T D S))
    (hd : Derives Gamma (StructuralListFieldSyntax.field w D z P))
    (hm : Derives Gamma (ForcingGuardCode.matrix order Reln w A f head q v))
    (hq : Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T q Y))
    (hv : Derives Gamma (SyntaxForestSyntax.forest 1 w (fun _ => P) V)) :
    Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted w V S (v 0) f z T (v 1) Y) := by
  have hf : Derives Gamma (frame w z (v 0) A f T head (v 2) (v 3) D S P V) :=
    .conjI hw (.conjI hz (.conjI (.conjL hm) (.conjI hh (.conjI (.conjL (.conjR (.conjR hm)))
      (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hm))))) (.conjI hl (.conjI hd hv)))))))
  have htV := ForcingAtomicCode.bound_forest_typed hZ w (v 0) z T V (fun _ => P)
    hw (.conjL hm) (.conjL hp) (fun _ => hp) hv
  have htN := Derives.conjR (.conjL (.conjR hm))
  have he := SyntaxMixedFormulaOutputInduction.actual_exists hZ w V S (v 0) f z T (v 1) hw (.conjI htN (.conjI htV (.conjR hl)))
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc V.castSucc S.castSucc (v 0).castSucc
    f.castSucc z.castSucc T.castSucc (v 1).castSucc (Fin.last m)
  let Delta := Context.add E (Context.image Formula.raise Gamma)
  apply Derives.exE (p := E) he
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  have hf1 := of_eq (frame_rename w z (v 0) A f T head (v 2) (v 3) D S P V Fin.castSucc) (SourceLogic.under hf E)
  have hm1 := of_eq (ForcingGuardCode.matrix_rename order Reln w A f head q v Fin.castSucc) (SourceLogic.under hm E)
  have hq1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S A f z T q Y Fin.castSucc) (SourceLogic.under hq E)
  have hfirst := Derives.conjR (.conjR (.conjR (.conjR (.conjR hm1))))
  have eq := formula (ZFContext.under hZ E) w.castSucc z.castSucc (v 0).castSucc A.castSucc f.castSucc T.castSucc
    head.castSucc (v 2).castSucc (v 3).castSucc D.castSucc S.castSucc P.castSucc V.castSucc
    (v 1).castSucc q.castSucc Y.castSucc (Fin.last m) hf1 (.conjI hfirst (.conjI hq1 hE))
  have out := SyntaxMixedFormulaJudgmentSubst.subst_q w.castSucc V.castSucc S.castSucc (v 0).castSucc
    f.castSucc z.castSucc T.castSucc (v 1).castSucc (Fin.last m) Y.castSucc (eq_symm eq) hE
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V S (v 0) f z T (v 1) Y Fin.castSucc).symm out

/-- Actual guard matrix followed by ONE raw query. The direct singleton
table and independent formula output are produced internally, then the
output is identified with SAME raw Y by the existing full cancellation. -/
theorem from_matrix {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (order : Bool) (Reln : Source.Formula (k+2)) (w z A f T D S P head q Y : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Gamma (omega w)) (hz : Derives Gamma (empty z))
    (hh : Derives Gamma (SyntaxVariableSyntax.code true w z head))
    (hp : Derives Gamma (SyntaxTermSyntax.term w z T P))
    (hl : Derives Gamma (SyntaxMixedImageCodeSyntax.termLists w A f z T D S))
    (hd : Derives Gamma (StructuralListFieldSyntax.field w D z P))
    (hm : Derives Gamma (ForcingGuardCode.matrix order Reln w A f head q v))
    (hq : Derives Gamma (SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T q Y)) :
    Derives Gamma (ForcingGuardOpening.direct w z f T P S (v 0) (v 1) Y) := by
  have he := SyntaxForests.exists_forest hZ 1 w (fun _ => P) hw (.conjI (SyntaxTerms.range hZ w z T P hw hp) (.eqRefl w))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj
    (SyntaxForestSyntax.forest 1 w.castSucc (fun _ => P.castSucc) (Fin.last m))
  let Delta := Context.add E (Context.image Formula.raise Gamma)
  apply Derives.exE (p := E) he
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  have out := at_bound_map (ZFContext.under hZ E) order Reln w.castSucc z.castSucc A.castSucc f.castSucc T.castSucc
    D.castSucc S.castSucc P.castSucc head.castSucc q.castSucc Y.castSucc (Fin.last m) (fun i => (v i).castSucc)
    (of_eq (omega_rename w Fin.castSucc) (SourceLogic.under hw E))
    (of_eq (empty_rename z Fin.castSucc) (SourceLogic.under hz E))
    (of_eq (SyntaxVariableSyntax.code_rename true w z head Fin.castSucc) (SourceLogic.under hh E))
    (of_eq (SyntaxTermSyntax.term_rename w z T P Fin.castSucc) (SourceLogic.under hp E))
    (of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w A f z T D S Fin.castSucc) (SourceLogic.under hl E))
    (of_eq (StructuralListFieldSyntax.field_rename w D z P Fin.castSucc) (SourceLogic.under hd E))
    (of_eq (ForcingGuardCode.matrix_rename order Reln w A f head q v Fin.castSucc) (SourceLogic.under hm E))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S A f z T q Y Fin.castSucc) (SourceLogic.under hq E)) (.conjR hE)
  have result : Derives Delta (ForcingGuardOpening.direct w.castSucc z.castSucc f.castSucc T.castSucc
      P.castSucc S.castSucc (v 0).castSucc (v 1).castSucc Y.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxForestSyntax.forest_rename,
      SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.conjI (.conjR hE) out)
  exact of_eq (ForcingGuardOpening.direct_rename w z f T P S (v 0) (v 1) Y Fin.castSucc).symm result

def compilerInput {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w z A f T D S P head q Y : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxVariableSyntax.code true w z head).conj
    ((SyntaxTermSyntax.term w z T P).conj ((SyntaxMixedImageCodeSyntax.termLists w A f z T D S).conj
      ((StructuralListFieldSyntax.field w D z P).conj ((ForcingGuardCode.compiled order Reln w A f head q).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T q Y)))))))

theorem compilerInput_rename {k m l} (order : Bool) (Reln : Source.Formula (k+2))
    (w z A f T D S P head q Y : Fin m) (rho : Fin m → Fin l) :
    (compilerInput order Reln w z A f T D S P head q Y).rename rho =
      compilerInput order Reln (rho w) (rho z) (rho A) (rho f) (rho T) (rho D) (rho S)
        (rho P) (rho head) (rho q) (rho Y) := by
  simp only [compilerInput, Formula.rename, omega_rename, empty_rename, SyntaxVariableSyntax.code_rename,
    SyntaxTermSyntax.term_rename, SyntaxMixedImageCodeSyntax.termLists_rename, StructuralListFieldSyntax.field_rename,
    ForcingGuardCode.compiled_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

/-- Both original member AND order compilers. All four compiler witnesses
and the direct singleton table are internal, with the actual free table S
preserved exactly; no fixed-layout or desired-output premise is required. -/
theorem from_compiled {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (order : Bool) (Reln : Source.Formula (k+2)) (w z A f T D S P head q Y : Fin m)
    (hi : Derives Gamma (compilerInput order Reln w z A f T D S P head q Y)) :
    Derives Gamma (ForcingGuardOpening.result order Reln w z f T P S A head q Y) := by
  have hc := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hi))))))
  let E := ForcingGuardCode.body order Reln w A f head q
  let Delta := Context.add E (raisedContext 4 Gamma)
  apply HornBinderRules.eliminate_many 4 E _ hc
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  have h := of_eq (compilerInput_rename order Reln w z A f T D S P head q Y (old 4)) (HornBinderRules.under_body 4 hi E)
  have h1 := Derives.conjR h
  have h2 := Derives.conjR h1
  have h3 := Derives.conjR h2
  have h4 := Derives.conjR h3
  have h5 := Derives.conjR h4
  have h6 := Derives.conjR h5
  have out := from_matrix (HornBinderRules.zf_body 4 hZ E) order Reln (old 4 w) (old 4 z) (old 4 A) (old 4 f)
    (old 4 T) (old 4 D) (old 4 S) (old 4 P) (old 4 head) (old 4 q) (old 4 Y) (slot 4)
    (.conjL h) (.conjL h1) (.conjL h2) (.conjL h3) (.conjL h4) (.conjL h5) hE (.conjR h6)
  have result : Derives Delta (ForcingGuardOpening.result order Reln (old 4 w) (old 4 z) (old 4 f) (old 4 T)
      (old 4 P) (old 4 S) (old 4 A) (old 4 head) (old 4 q) (old 4 Y)) := by
    apply HornBinderRules.intro_many 4 _ (slot 4)
    exact of_eq (by simp only [ForcingGuardOpening.body, ForcingGuardOpening.data_rename, assign_old, assign_slot]; rfl)
      (.conjI hE out)
  exact of_eq (ForcingGuardOpening.result_rename order Reln w z f T P S A head q Y (old 4)).symm result

def compilerSentence {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w z A f T D S P head q Y : Fin m) : Source.Sentence :=
  ((compilerInput order Reln w z A f T D S P head q Y).imp
    (ForcingGuardOpening.result order Reln w z f T P S A head q Y)).close

theorem compiler_kernel_certificate {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w z A f T D S P head q Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (compilerSentence order Reln w z A f T D S P head q Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_compiled (ZFContext.add (ZFContext.source_ZF m) _) order Reln w z A f T D S P head q Y (.hyp (Or.inl rfl))

def openedInput {k m} (order : Bool) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S n x Parent own head q Y : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Formula m :=
  (ForcingFreshParentOpening.data w z a f alpha b A B t R S n x Parent v u).conj
    ((SyntaxMixedImageHead.head w alpha f own head).conj
      ((ForcingGuardCode.compiled order Reln w alpha f head q).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w (u 7) (v 9) alpha f z B q Y)))

theorem openedInput_rename {k m l} (order : Bool) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S n x Parent own head q Y : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) (rho : Fin m → Fin l) :
    (openedInput order Reln w z a f alpha b A B t R S n x Parent own head q Y v u).rename rho =
      openedInput order Reln (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t)
        (rho R) (rho S) (rho n) (rho x) (rho Parent) (rho own) (rho head) (rho q) (rho Y)
        (fun i => rho (v i)) (fun i => rho (u i)) := by
  simp only [openedInput, Formula.rename, ForcingFreshParentOpening.data_rename, SyntaxMixedImageHead.head_rename,
    ForcingGuardCode.compiled_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

/-- ACTUAL consumer of the accepted whole-parent opening. Its cons table
generates the needed bound-zero field internally. List types come from the
same weak-image records and source successor. The compiler's own zero is
internally aligned; no supplied field/type/body/map-equality answer. -/
theorem from_opened {k m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (order : Bool) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S n x Parent own head q Y : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m)
    (hi : Derives Gamma (openedInput order Reln w z a f alpha b A B t R S n x Parent own head q Y v u)) :
    Derives Gamma (ForcingGuardOpening.result order Reln w z f B t (v 9) alpha head q Y) := by
  have hop := Derives.conjL hi
  have source := Derives.conjL hop
  have hw := Derives.conjL source
  have hz := Derives.conjL (.conjR source)
  have hs := Derives.conjL (.conjR (.conjR source))
  have ht := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR source))))))
  have images := Derives.conjL (.conjR hop)
  have lists := SyntaxMixedImageCodePairs.term_lists w (v 6) (v 7) a f z B (v 8) (v 9)
    (.conjR (.conjR (.conjR (.conjR images))))
  have cons := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hop)))))))
  have typedD := TypedArgumentListConstruction.cons_list hZ w a alpha z B t (v 8) (u 7) hw ht (.conjL lists) cons hs
  have typed : Derives Gamma (SyntaxMixedImageCodeSyntax.termLists w alpha f z B (u 7) (v 9)) :=
    .conjI typedD (.conjR lists)
  have zero := StructuralListFieldCons.zero_value hZ w t (v 8) (u 7) z hw (SyntaxTerms.range hZ w z B t hw ht)
    (.conjL (.conjL (.conjR (.conjR (.conjL lists))))) cons hz
  have hh := Derives.conjL (.conjR hi)
  have oz := OmegaUniversal.empty_unique own z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) hz
  have head0 := SyntaxVariableImagePoint.code_subst_index true w own head z oz (.conjL (.conjR hh))
  exact from_compiled hZ order Reln w z alpha f B (u 7) (v 9) t head q Y
    (.conjI hw (.conjI hz (.conjI head0 (.conjI ht (.conjI typed (.conjI zero
      (.conjI (.conjL (.conjR (.conjR hi))) (.conjR (.conjR (.conjR hi))))))))))

def openedSentence {k m} (order : Bool) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S n x Parent own head q Y : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) : Source.Sentence :=
  ((openedInput order Reln w z a f alpha b A B t R S n x Parent own head q Y v u).imp
    (ForcingGuardOpening.result order Reln w z f B t (v 9) alpha head q Y)).close

theorem opened_kernel_certificate {k m} (order : Bool) (Reln : Source.Formula (k+2))
    (w z a f alpha b A B t R S n x Parent own head q Y : Fin m)
    (v : Fin 10 → Fin m) (u : Fin 9 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (openedSentence order Reln w z a f alpha b A B t R S n x Parent own head q Y v u)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_opened (ZFContext.add (ZFContext.source_ZF m) _) order Reln
    w z a f alpha b A B t R S n x Parent own head q Y v u (.hyp (Or.inl rfl))

/- Only fixed record-slot bookkeeping: SAME old WeakOverwrite metadata,
with its actual two changed free graphs and SAME actual New list. -/
private def overwriteImages {m} (v : Fin 10 → Fin m) (g h New : Fin m) : Fin 10 → Fin m :=
  Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3) (Fin.cases (v 4)
    (Fin.cases g (Fin.cases (v 6) (Fin.cases h (SyntaxAtomSyntax.two (v 8) New))))))))

private theorem overwriteImages_map {m l} (v : Fin 10 → Fin m) (g h New : Fin m) (rho : Fin m → Fin l) :
    (fun i => rho (overwriteImages v g h New i)) = overwriteImages (fun i => rho (v i)) (rho g) (rho h) (rho New) := by
  funext i
  rcases i with ⟨i,hi⟩
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def overwrittenBody {m} (w z a f alpha b A B t R Old New n x Parent : Fin m) (v : Fin 10 → Fin m) : Formula (m+2) :=
  ForcingFreshParentOpening.atImages (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 alpha) (old 2 b) (old 2 A) (old 2 B)
    (old 2 t) (old 2 R) (old 2 Old) (old 2 n) (old 2 x) (old 2 Parent)
    (overwriteImages (fun i => old 2 (v i)) (slot 2 0) (slot 2 1) (old 2 New))

def overwritten {m} (w z a f alpha b A B t R Old New n x Parent : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  existsMany 2 (overwrittenBody w z a f alpha b A B t R Old New n x Parent v)

theorem overwritten_rename {m l} (w z a f alpha b A B t R Old New n x Parent : Fin m)
    (v : Fin 10 → Fin m) (rho : Fin m → Fin l) :
    (overwritten w z a f alpha b A B t R Old New n x Parent v).rename rho =
      overwritten (rho w) (rho z) (rho a) (rho f) (rho alpha) (rho b) (rho A) (rho B) (rho t)
        (rho R) (rho Old) (rho New) (rho n) (rho x) (rho Parent) (fun i => rho (v i)) := by
  simp only [overwritten, existsMany_rename, overwrittenBody, ForcingFreshParentOpening.atImages_rename,
    overwriteImages_map, lift_old, lift_slot]

def overwrittenInput {m} (w z a f alpha b A B t R S j Q Qn Old New n x Parent : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (ForcingWeakenedOverwrite.frame w a f z b B R S j Q Qn Old New v).conj
    (ForcingFreshParentOpening.input w z a f alpha b A B t R Old n x Parent)

/-- Use the ALREADY produced canonical replacement New, not an independent
weak-image table followed by a new table-equality problem. The existing
WeakOverwrite producer supplies its two actual free graphs. Feed its SAME
record into the unchanged FreshParentOpening private proof via its public
produce_at_images wrapper; all nineteen actual opening outputs remain EX. -/
theorem open_overwritten {m} {Gamma : Context m} (hZ : ZFContext.Evidence Gamma)
    (w z a f alpha b A B t R S j Q Qn Old New n x Parent : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Gamma (overwrittenInput w z a f alpha b A B t R S j Q Qn Old New n x Parent v)) :
    Derives Gamma (overwritten w z a f alpha b A B t R Old New n x Parent v) := by
  have he := ForcingWeakenedOverwrite.produce hZ w a f z b B R S j Q Qn Old New v (.conjL hi)
  let E := ForcingWeakenedOverwrite.resultBody w a f z b B R Old New v
  let Delta := Context.add E (raisedContext 2 Gamma)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Delta E := .hyp (Or.inl rfl)
  let vv := overwriteImages (fun i => old 2 (v i)) (slot 2 0) (slot 2 1) (old 2 New)
  have images : Derives Delta (ForcingWeakenedImages.data (old 2 w) (old 2 a) (old 2 f) (old 2 z) (old 2 b)
      (old 2 B) (old 2 R) (old 2 Old) vv) := hE
  have ho := ForcingFreshParentOpening.produce_at_images (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 alpha) (old 2 b) (old 2 A) (old 2 B) (old 2 t)
    (old 2 R) (old 2 Old) (old 2 n) (old 2 x) (old 2 Parent) vv
    (of_eq (ForcingFreshParentOpening.input_rename w z a f alpha b A B t R Old n x Parent (old 2))
      (HornBinderRules.under_body 2 (.conjR hi) E)) images
  have result : Derives Delta (overwritten (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 alpha) (old 2 b) (old 2 A)
      (old 2 B) (old 2 t) (old 2 R) (old 2 Old) (old 2 New) (old 2 n) (old 2 x) (old 2 Parent) (fun i => old 2 (v i))) := by
    apply HornBinderRules.intro_many 2 _ (slot 2)
    exact of_eq (by simp only [overwrittenBody, ForcingFreshParentOpening.atImages_rename,
      overwriteImages_map, assign_old, assign_slot]; rfl) ho
  exact of_eq (overwritten_rename w z a f alpha b A B t R Old New n x Parent v (old 2)).symm result

def overwrittenSentence {m} (w z a f alpha b A B t R S j Q Qn Old New n x Parent : Fin m)
    (v : Fin 10 → Fin m) : Source.Sentence :=
  ((overwrittenInput w z a f alpha b A B t R S j Q Qn Old New n x Parent v).imp
    (overwritten w z a f alpha b A B t R Old New n x Parent v)).close

theorem overwritten_kernel_certificate {m} (w z a f alpha b A B t R S j Q Qn Old New n x Parent : Fin m)
    (v : Fin 10 → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (overwrittenSentence w z a f alpha b A B t R S j Q Qn Old New n x Parent v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact open_overwritten (ZFContext.add (ZFContext.source_ZF m) _) w z a f alpha b A B t R S j Q Qn Old New n x Parent v
    (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingRawGuardOpening
