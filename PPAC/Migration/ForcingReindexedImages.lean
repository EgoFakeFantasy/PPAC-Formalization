import PPAC.Migration.ForcingBinderFormula
import PPAC.Migration.Internal.SyntaxTermImagePushBoth

/-! Reuse the original target-index push of BOTH complete term-image graphs.
The old decoded graphs, pushed graphs and new original list codes are produced
under six object existential binders. No pointwise map answer is an input. -/
namespace PPAC.Migration.ForcingReindexedImages
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxMixedImageCodeSyntax (encodings encodings_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def data {m} (w a b c d C D R S I J : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (encodings w (v 0) (v 1) a b c d R S).conj
    ((SyntaxTermImagePushBoth.both w I J c d C D (v 0) (v 1) a b (v 2) (v 3)).conj
      (encodings w (v 2) (v 3) a b C D (v 4) (v 5)))

theorem data_rename {m l} (w a b c d C D R S I J : Fin m) (v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (data w a b c d C D R S I J v).rename ρ =
      data (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) (ρ D) (ρ R) (ρ S) (ρ I) (ρ J) (fun i => ρ (v i)) := by
  simp only [data, Formula.rename, encodings_rename, SyntaxTermImagePushBoth.both_rename]

def body {m} (w a b c d C D R S I J : Fin m) : Formula (m+6) :=
  data (old 6 w) (old 6 a) (old 6 b) (old 6 c) (old 6 d) (old 6 C) (old 6 D)
    (old 6 R) (old 6 S) (old 6 I) (old 6 J) (slot 6)

def produced {m} (w a b c d C D R S I J : Fin m) : Formula m :=
  existsMany 6 (body w a b c d C D R S I J)

theorem produced_rename {m l} (w a b c d C D R S I J : Fin m) (ρ : Fin m → Fin l) :
    (produced w a b c d C D R S I J).rename ρ =
      produced (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) (ρ D) (ρ R) (ρ S) (ρ I) (ρ J) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem at_push {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d C D R S I J r s g h : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encodings w r s a b c d R S))
    (hp : Derives Γ (SyntaxTermImagePushBoth.both w I J c d C D r s a b g h)) :
    Derives Γ (produced w a b c d C D R S I J) := by
  let E := encodings (old 2 w) (old 2 g) (old 2 h) (old 2 a) (old 2 b) (old 2 C) (old 2 D) (slot 2 0) (slot 2 1)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _
    (SyntaxMixedImageCodePairs.exists_codes hZ w g h a b C D hw
      (SyntaxTermImagePushBoth.target_maps w I J c d C D r s a b g h hp))
  have he2 := of_eq (encodings_rename w r s a b c d R S (old 2)) (HornBinderRules.under_body 2 he E)
  have hp2 := of_eq (SyntaxTermImagePushBoth.both_rename w I J c d C D r s a b g h (old 2))
    (HornBinderRules.under_body 2 hp E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hd : Derives Δ (data (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 C) (old 2 D)
      (old 2 R) (old 2 S) (old 2 I) (old 2 J)
      (Fin.cases (old 2 r) (Fin.cases (old 2 s) (Fin.cases (old 2 g) (Fin.cases (old 2 h) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1))))))) :=
    .conjI he2 (.conjI hp2 hE)
  have ho : Derives Δ (produced (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 C) (old 2 D)
      (old 2 R) (old 2 S) (old 2 I) (old 2 J)) := by
    apply HornBinderRules.intro_many 6 _
      (Fin.cases (old 2 r) (Fin.cases (old 2 s) (Fin.cases (old 2 g) (Fin.cases (old 2 h) (SyntaxAtomSyntax.two (slot 2 0) (slot 2 1))))))
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  exact of_eq (produced_rename w a b c d C D R S I J (old 2)).symm ho

private theorem at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d C D R S I J r s : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxIndexMapSyntax.maps w I J c d C D))
    (he : Derives Γ (encodings w r s a b c d R S)) : Derives Γ (produced w a b c d C D R S I J) := by
  let E := SyntaxTermImagePushBoth.both (old 2 w) (old 2 I) (old 2 J) (old 2 c) (old 2 d) (old 2 C) (old 2 D)
    (old 2 r) (old 2 s) (old 2 a) (old 2 b) (slot 2 0) (slot 2 1)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _
    (SyntaxTermImagePushBoth.exists_both hZ w I J c d C D r s a b hw hm
      (.conjI (.conjL (.conjL he)) (.conjL (.conjR he))))
  have ho := at_push (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 C) (old 2 D)
    (old 2 R) (old 2 S) (old 2 I) (old 2 J) (old 2 r) (old 2 s) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (encodings_rename w r s a b c d R S (old 2)) (HornBinderRules.under_body 2 he E)) (.hyp (Or.inl rfl))
  exact of_eq (produced_rename w a b c d C D R S I J (old 2)).symm ho

/-- Complete original graph/list operations, not supplied covariance laws. -/
theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c d C D R S I J : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxIndexMapSyntax.maps w I J c d C D))
    (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d R S)) :
    Derives Γ (produced w a b c d C D R S I J) := by
  let E := encodings (old 2 w) (slot 2 0) (slot 2 1) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 R) (old 2 S)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ (SyntaxMixedImageCodePairs.exists_graphs hZ w a b c d R S hw ht)
  have ho := at_graphs (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 C) (old 2 D)
    (old 2 R) (old 2 S) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E))
    (of_eq (SyntaxIndexMapSyntax.maps_rename w I J c d C D (old 2)) (HornBinderRules.under_body 2 hm E)) (.hyp (Or.inl rfl))
  exact of_eq (produced_rename w a b c d C D R S I J (old 2)).symm ho

/-- Each actual new field is the original target rename of the SAME old
field. Source bound/free is only a selector; its output category is arbitrary. -/
theorem field_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w a b c d C D R S I J i u t : Fin m) (v : Fin 6 → Fin m)
    (hd : Derives Γ (data w a b c d C D R S I J v))
    (hu : Derives Γ ((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound R S) i u))) :
    Derives Γ (((Formula.mem i (SyntaxTermSyntax.limit bound a b)).conj
      (StructuralListFieldSyntax.field w (SyntaxIndexMapSyntax.selectMap bound (v 4) (v 5)) i t)).iff
      (SyntaxRenameTermSyntax.renamed w I J c d C D u t)) := by
  have he := SyntaxCodedMixedTermFields.selected_encoded bound w (v 0) (v 1) a b c d R S (.conjL hd)
  have hn := SyntaxCodedMixedTermFields.selected_encoded bound w (v 2) (v 3) a b C D (v 4) (v 5) (.conjR (.conjR hd))
  have hp : Derives Γ (SyntaxTermImagePushSyntax.pushed w I J c d C D
      (SyntaxIndexMapSyntax.selectMap bound (v 0) (v 1)) (SyntaxTermSyntax.limit bound a b)
      (SyntaxIndexMapSyntax.selectMap bound (v 2) (v 3))) := by
    cases bound
    · exact .conjR (.conjL (.conjR hd))
    · exact .conjL (.conjL (.conjR hd))
  have hEdge := Derives.impE (.conjR (SyntaxMixedImageCodeFields.edges _ _ _ _ _ _ _ _ he)) hu
  have hPush := SyntaxTermImagePushGraph.at_value hZ w I J c d C D
    (SyntaxIndexMapSyntax.selectMap bound (v 0) (v 1)) (SyntaxTermSyntax.limit bound a b)
    (SyntaxIndexMapSyntax.selectMap bound (v 2) (v 3)) i u t hp hEdge
  have hNew := SyntaxMixedImageCodeFields.edges _ _ _ _ _ _ i t hn
  exact SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hNew) (.conjL hNew)) hPush

private def termInput {m} (w a b c d C D R S I J F G P Q x u t o : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (omega w).conj ((data w a b c d C D R S I J v).conj
    ((IndexTermRenameTransportSyntax.realization w I J F G c d C D P Q).conj
      ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d x u).conj
        ((SyntaxCodedMixedTermSyntax.substituted w P Q c d C D u t).conj
          (SyntaxCodedMixedTermSyntax.substituted w (v 4) (v 5) a b C D x o)))))

private theorem termInput_rename {m l} (w a b c d C D R S I J F G P Q x u t o : Fin m)
    (v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (termInput w a b c d C D R S I J F G P Q x u t o v).rename ρ =
      termInput (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) (ρ D) (ρ R) (ρ S) (ρ I) (ρ J)
        (ρ F) (ρ G) (ρ P) (ρ Q) (ρ x) (ρ u) (ρ t) (ρ o) (fun i => ρ (v i)) := by
  simp only [termInput, Formula.rename, omega_rename, data_rename,
    IndexTermRenameTransportSyntax.realization_rename, SyntaxCodedMixedTermSyntax.substituted_rename]

/-- The root term comparison follows the SAME old and newly produced
fields. Arbitrary internal indices are eliminated by the existing two
variable branches; the desired comparison is never an input. -/
private theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d C D R S I J F G P Q x u t o : Fin m) (v : Fin 6 → Fin m)
    (hi : Derives Γ (termInput w a b c d C D R S I J F G P Q x u t o v)) :
    Derives Γ (.equal t o) := by
  have h0 := Derives.conjL (.conjR (.conjR (.conjR hi)))
  have ht := SyntaxCodedMixedTermTyping.source_type w R S a b c d x u h0
  apply OriginalTermScopeElimination.eliminate w a b x (.equal t o) ht
  intro bound
  let E := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a b) x
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have h1 := of_eq (termInput_rename w a b c d C D R S I J F G P Q x u t o v Fin.castSucc) (under hi E)
  have hw1 := Derives.conjL h1
  have hd := Derives.conjL (.conjR h1)
  have hr := Derives.conjL (.conjR (.conjR h1))
  have hOld := Derives.conjL (.conjR (.conjR (.conjR h1)))
  have hNext := Derives.conjL (.conjR (.conjR (.conjR (.conjR h1))))
  have hNew := Derives.conjR (.conjR (.conjR (.conjR (.conjR h1))))
  have hCode : Derives Δ (SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) x.castSucc) := .conjR hE
  have hOldLists := SyntaxMixedImageCodePairs.term_lists _ _ _ _ _ _ _ _ _ (.conjL hd)
  have hOldField := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 bound
    w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc u.castSucc (Fin.last m)
    hw1 hOldLists hCode)) hOld
  have hNewLists := SyntaxMixedImageCodePairs.term_lists _ _ _ _ _ _ _ _ _ (.conjR (.conjR hd))
  have hNewField := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 bound
    w.castSucc (v 4).castSucc (v 5).castSucc a.castSucc b.castSucc C.castSucc D.castSucc x.castSucc o.castSucc (Fin.last m)
    hw1 hNewLists hCode)) hNew
  have hDirect := Derives.impE (.conjL (field_iff hZ1 bound
    w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc C.castSucc D.castSucc R.castSucc S.castSucc I.castSucc J.castSucc
    (Fin.last m) u.castSucc o.castSucc (fun i => (v i).castSucc) hd hOldField)) hNewField
  have hSequential := IndexTermRenameTransport.term_reverse hZ1
    w.castSucc I.castSucc J.castSucc F.castSucc G.castSucc c.castSucc d.castSucc C.castSucc D.castSucc
    P.castSucc Q.castSucc u.castSucc t.castSucc hw1 hr hNext
  exact SyntaxRenameTermUnique.unique hZ1 w.castSucc I.castSucc J.castSucc c.castSucc d.castSucc C.castSucc D.castSucc
    u.castSucc t.castSucc o.castSucc hw1 hSequential hDirect

private def four {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private def frame {m} (w a b c d C D R S I J F G P Q I2 J2 R2 S2 : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (omega w).conj ((data w a b c d C D R S I J v).conj
    ((IndexTermRenameTransportSyntax.realization w I J F G c d C D P Q).conj
      ((SyntaxIdentityMapSyntax.identityCode w C I2).conj
        ((SyntaxIdentityMapSyntax.identityCode w D J2).conj
          (IndexTermImageCodeSyntax.environment w I2 J2 R2 S2 C D C D)))))

private theorem frame_rename {m l} (w a b c d C D R S I J F G P Q I2 J2 R2 S2 : Fin m)
    (v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (frame w a b c d C D R S I J F G P Q I2 J2 R2 S2 v).rename ρ =
      frame (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) (ρ D) (ρ R) (ρ S) (ρ I) (ρ J)
        (ρ F) (ρ G) (ρ P) (ρ Q) (ρ I2) (ρ J2) (ρ R2) (ρ S2) (fun i => ρ (v i)) := by
  simp only [frame, Formula.rename, omega_rename, data_rename, IndexTermRenameTransportSyntax.realization_rename,
    SyntaxIdentityMapSyntax.identityCode_rename, IndexTermImageCodeSyntax.environment_rename]

private theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d C D R S I J F G P Q I2 J2 R2 S2 : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w a b c d C D R S I J F G P Q I2 J2 R2 S2 v)) :
    Derives Γ (ForcingTermDiagram.diagram w (four a c C C) (four b d D D)
      (four R P R2 (v 4)) (four S Q S2 (v 5))) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := (ForcingTermDiagram.step (old 5 w) (four (old 5 a) (old 5 c) (old 5 C) (old 5 C))
      (four (old 5 b) (old 5 d) (old 5 D) (old 5 D))
      (four (old 5 R) (old 5 P) (old 5 R2) (old 5 (v 4))) (four (old 5 S) (old 5 Q) (old 5 S2) (old 5 (v 5)))
      0 (slot 5 0) (slot 5 1)).conj
    ((ForcingTermDiagram.step (old 5 w) (four (old 5 a) (old 5 c) (old 5 C) (old 5 C))
      (four (old 5 b) (old 5 d) (old 5 D) (old 5 D))
      (four (old 5 R) (old 5 P) (old 5 R2) (old 5 (v 4))) (four (old 5 S) (old 5 Q) (old 5 S2) (old 5 (v 5)))
      1 (slot 5 1) (slot 5 2)).conj
      ((ForcingTermDiagram.step (old 5 w) (four (old 5 a) (old 5 c) (old 5 C) (old 5 C))
      (four (old 5 b) (old 5 d) (old 5 D) (old 5 D))
      (four (old 5 R) (old 5 P) (old 5 R2) (old 5 (v 4))) (four (old 5 S) (old 5 Q) (old 5 S2) (old 5 (v 5)))
      2 (slot 5 2) (slot 5 3)).conj
        (ForcingTermDiagram.step (old 5 w) (four (old 5 a) (old 5 c) (old 5 C) (old 5 C))
      (four (old 5 b) (old 5 d) (old 5 D) (old 5 D))
      (four (old 5 R) (old 5 P) (old 5 R2) (old 5 (v 4))) (four (old 5 S) (old 5 Q) (old 5 S2) (old 5 (v 5)))
      3 (slot 5 0) (slot 5 4))))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h5 := of_eq (frame_rename w a b c d C D R S I J F G P Q I2 J2 R2 S2 v (old 5))
    (HornBinderRules.under_body 5 hf E)
  have hZ5 := HornBinderRules.zf_body 5 hZ E
  have hw := Derives.conjL h5
  have hData := Derives.conjL (.conjR h5)
  have hReal := Derives.conjL (.conjR (.conjR h5))
  have hI := Derives.conjL (.conjR (.conjR (.conjR h5)))
  have hJ := Derives.conjL (.conjR (.conjR (.conjR (.conjR h5))))
  have hEnv := Derives.conjR (.conjR (.conjR (.conjR (.conjR h5))))
  have hTO := term hZ5 (old 5 w) (old 5 a) (old 5 b) (old 5 c) (old 5 d) (old 5 C) (old 5 D)
    (old 5 R) (old 5 S) (old 5 I) (old 5 J) (old 5 F) (old 5 G) (old 5 P) (old 5 Q)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 4) (fun i => old 5 (v i))
    (.conjI hw (.conjI hData (.conjI hReal (.conjI (.conjL hE) (.conjI (.conjL (.conjR hE)) (.conjR (.conjR (.conjR hE))))))))
  have hTY := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 C) (old 5 D)
    (old 5 I2) (old 5 J2) (old 5 R2) (old 5 S2) (slot 5 2) (slot 5 3)
    hw hI hJ hEnv (.conjL (.conjR (.conjR hE)))
  exact eq_trans (eq_symm hTY) hTO

/-- Consume three actual queries and the generated push records. The
EXISTING full formula cancellation handles every internal formula and binder;
there is no new formula induction or externally-standard code restriction. -/
private theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d C D R S I J F G P Q I2 J2 R2 S2 n u t o : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w a b c d C D R S I J F G P Q I2 J2 R2 S2 v))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w P Q c d C D u t))
    (h3 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 4) (v 5) a b C D n o)) :
    Derives Γ (.equal t o) := by
  have hw := Derives.conjL hf
  have hI := Derives.conjL (.conjR (.conjR (.conjR hf)))
  have hJ := Derives.conjL (.conjR (.conjR (.conjR (.conjR hf))))
  have hEnv := Derives.conjR (.conjR (.conjR (.conjR (.conjR hf))))
  have ht := SyntaxMixedFormulaJudgment.target_type w P Q c d C D u t h1
  have hSelf := SyntaxIdentityInduction.reflexive hZ w I2 J2 C D t hw hI hJ ht
  have h2 := IndexFormulaRenameInduction.forward hZ w I2 J2 R2 S2 C D C D t t hw hEnv hSelf
  exact ForcingFormulaInduction.cancel hZ w (four a c C C) (four b d D D)
    (four R P R2 (v 4)) (four S Q S2 (v 5)) n u t t o hw
    (term_diagram hZ w a b c d C D R S I J F G P Q I2 J2 R2 S2 v hf) h0 h1 h2 h3

def comparisonInput {m} (w a b c d C D R S I J F G P Q n u t o : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (omega w).conj ((data w a b c d C D R S I J v).conj
    ((IndexTermRenameTransportSyntax.realization w I J F G c d C D P Q).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n u).conj
        ((SyntaxMixedFormulaJudgmentSyntax.substituted w P Q c d C D u t).conj
          (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 4) (v 5) a b C D n o)))))

theorem comparisonInput_rename {m l} (w a b c d C D R S I J F G P Q n u t o : Fin m)
    (v : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (comparisonInput w a b c d C D R S I J F G P Q n u t o v).rename ρ =
      comparisonInput (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ C) (ρ D) (ρ R) (ρ S) (ρ I) (ρ J)
        (ρ F) (ρ G) (ρ P) (ρ Q) (ρ n) (ρ u) (ρ t) (ρ o) (fun i => ρ (v i)) := by
  simp only [comparisonInput, Formula.rename, omega_rename, data_rename,
    IndexTermRenameTransportSyntax.realization_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

/-- Produce and eliminate all four identity-index/image witnesses. Only
actual push/realization records and three actual formula queries remain. -/
theorem compare {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d C D R S I J F G P Q n u t o : Fin m) (v : Fin 6 → Fin m)
    (hi : Derives Γ (comparisonInput w a b c d C D R S I J F G P Q n u t o v)) : Derives Γ (.equal t o) := by
  have hw := Derives.conjL hi
  have hr := Derives.conjL (.conjR (.conjR hi))
  have hm := IndexTermRenameTransportSyntax.index_maps _ _ _ _ _ _ _ _ _ _ _ hr
  have hc := SyntaxIndexMapSyntax.target_contexts w I J c d C D hm
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc C.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxIdentityCode.exists_code hZ w C hw (.conjL hc))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  let H := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc D.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add H (Context.image Formula.raise Δ)
  apply Derives.exE (p := H) (SyntaxIdentityCode.exists_code hZ1 w.castSucc D.castSucc hw1 (under (.conjR hc) E))
  have hH : Derives Ξ H := .hyp (Or.inl rfl)
  have hI : Derives Ξ (SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 C) (slot 2 0)) :=
    of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc C.castSucc (Fin.last m) Fin.castSucc) (under hE H)
  have hZ2 := ZFContext.under hZ1 H
  have hw2 : Derives Ξ (omega (old 2 w)) :=
    of_eq (by simp only [Formula.raise, omega_rename]; rfl) (under hw1 H)
  have hi2 : Derives Ξ (comparisonInput (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 C) (old 2 D)
      (old 2 R) (old 2 S) (old 2 I) (old 2 J) (old 2 F) (old 2 G) (old 2 P) (old 2 Q)
      (old 2 n) (old 2 u) (old 2 t) (old 2 o) (fun i => old 2 (v i))) :=
    of_eq (by simp only [Formula.raise, comparisonInput_rename]; rfl) (under (under hi E) H)
  let K := IndexTermImageCodeSyntax.environment (old 4 w) (old 2 (slot 2 0)) (old 2 (slot 2 1))
    (slot 2 0) (slot 2 1) (old 4 C) (old 4 D) (old 4 C) (old 4 D)
  let Ω := Context.add K (raisedContext 2 Ξ)
  apply HornBinderRules.eliminate_many 2 K _
    (IndexTermImageEnvironment.exists_environment hZ2 (old 2 w) (slot 2 0) (slot 2 1)
      (old 2 C) (old 2 D) (old 2 C) (old 2 D) hw2
      (SyntaxIdentityCode.map_code _ _ _ hI) (SyntaxIdentityCode.map_code _ _ _ hH))
  have hK : Derives Ω K := .hyp (Or.inl rfl)
  have h4 : Derives Ω (comparisonInput (old 4 w) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 C) (old 4 D)
      (old 4 R) (old 4 S) (old 4 I) (old 4 J) (old 4 F) (old 4 G) (old 4 P) (old 4 Q)
      (old 4 n) (old 4 u) (old 4 t) (old 4 o) (fun i => old 4 (v i))) :=
    of_eq (by simp only [comparisonInput_rename]; rfl) (HornBinderRules.under_body 2 hi2 K)
  have hI4 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename (old 2 w) (old 2 C) (slot 2 0) (old 2))
    (HornBinderRules.under_body 2 hI K)
  have hJ4 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename (old 2 w) (old 2 D) (slot 2 1) (old 2))
    (HornBinderRules.under_body 2 hH K)
  have hf : Derives Ω (frame (old 4 w) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 C) (old 4 D)
      (old 4 R) (old 4 S) (old 4 I) (old 4 J) (old 4 F) (old 4 G) (old 4 P) (old 4 Q)
      (old 2 (slot 2 0)) (old 2 (slot 2 1)) (slot 2 0) (slot 2 1) (fun i => old 4 (v i))) :=
    .conjI (.conjL h4) (.conjI (.conjL (.conjR h4)) (.conjI (.conjL (.conjR (.conjR h4))) (.conjI hI4 (.conjI hJ4 hK))))
  exact formula (HornBinderRules.zf_body 2 hZ2 K)
    (old 4 w) (old 4 a) (old 4 b) (old 4 c) (old 4 d) (old 4 C) (old 4 D)
    (old 4 R) (old 4 S) (old 4 I) (old 4 J) (old 4 F) (old 4 G) (old 4 P) (old 4 Q)
    (old 2 (slot 2 0)) (old 2 (slot 2 1)) (slot 2 0) (slot 2 1)
    (old 4 n) (old 4 u) (old 4 t) (old 4 o) (fun i => old 4 (v i)) hf
    (.conjL (.conjR (.conjR (.conjR h4)))) (.conjL (.conjR (.conjR (.conjR (.conjR h4)))))
    (.conjR (.conjR (.conjR (.conjR (.conjR h4)))))

def comparisonSentence {m} (w a b c d C D R S I J F G P Q n u t o : Fin m) (v : Fin 6 → Fin m) : Source.Sentence :=
  ((comparisonInput w a b c d C D R S I J F G P Q n u t o v).imp (.equal t o)).close

theorem comparison_kernel_certificate {m} (w a b c d C D R S I J F G P Q n u t o : Fin m) (v : Fin 6 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (comparisonSentence w a b c d C D R S I J F G P Q n u t o v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact compare (ZFContext.add (ZFContext.source_ZF m) _) w a b c d C D R S I J F G P Q n u t o v (.hyp (Or.inl rfl))

def produceSentence {m} (w a b c d C D R S I J : Fin m) : Source.Sentence :=
  (((omega w).conj ((SyntaxIndexMapSyntax.maps w I J c d C D).conj
    (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))).imp (produced w a b c d C D R S I J)).close

theorem produce_kernel_certificate {m} (w a b c d C D R S I J : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (produceSentence w a b c d C D R S I J)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (omega w).conj ((SyntaxIndexMapSyntax.maps w I J c d C D).conj
    (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))
  have h : Derives (Context.add E (Source.SetLanguage.ZF.at m)) E := .hyp (Or.inl rfl)
  exact produce (ZFContext.add (ZFContext.source_ZF m) E) w a b c d C D R S I J
    (.conjL h) (.conjL (.conjR h)) (.conjR (.conjR h))

end PPAC.Migration.ForcingReindexedImages
