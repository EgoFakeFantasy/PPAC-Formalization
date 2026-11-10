import PPAC.Migration.ForcingRawGuardOpening
import PPAC.Migration.ForcingRebindTerms

/-! Cancel the original negative operand's condition rebind against the
actual fresh parent opening. The selected condition becomes the cons head. -/
namespace PPAC.Migration.ForcingRawNegTail
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field)
open SyntaxCodedMixedTermSyntax (substituted)
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def frame {m} (w z f B R D S Base j t Q E : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxTermSyntax.term w z B t).conj
    ((StructuralListSyntax.consCode w t R D).conj
      ((ForcingReflexiveImages.replacement w f z B Base j Q S).conj
        (ForcingReflexiveImages.replacement w f z B Base j t E)))))

private theorem frame_rename {m l} (w z f B R D S Base j t Q E : Fin m) (ρ : Fin m → Fin l) :
    (frame w z f B R D S Base j t Q E).rename ρ =
      frame (ρ w) (ρ z) (ρ f) (ρ B) (ρ R) (ρ D) (ρ S) (ρ Base) (ρ j) (ρ t) (ρ Q) (ρ E) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, SyntaxTermSyntax.term_rename,
    StructuralListSyntax.consCode_rename, ForcingReflexiveImages.replacement_rename]

private def path {m} (w z a alpha f B R D S E x y out direct : Fin m)
    (cv : Fin 6 → Fin m) : Formula m :=
  (substituted w (cv 3) (cv 5) a f alpha f x y).conj
    ((substituted w D S alpha f z B y out).conj (substituted w R E a f z B x direct))

private theorem path_rename {m l} (w z a alpha f B R D S E x y out direct : Fin m)
    (cv : Fin 6 → Fin m) (ρ : Fin m → Fin l) :
    (path w z a alpha f B R D S E x y out direct cv).rename ρ =
      path (ρ w) (ρ z) (ρ a) (ρ alpha) (ρ f) (ρ B) (ρ R) (ρ D) (ρ S) (ρ E)
        (ρ x) (ρ y) (ρ out) (ρ direct) (fun i => ρ (cv i)) := by
  simp only [path, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

private structure Inputs {m} (Γ : Context m) (w z a alpha f B R D S Base j t Q E n q x y out direct : Fin m)
    (cv : Fin 6 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  frame : Derives Γ (frame w z f B R D S Base j t Q E)
  compiler : Derives Γ (ForcingConditionRebind.data w a f alpha j n q cv)
  path : Derives Γ (path w z a alpha f B R D S E x y out direct cv)

private theorem Inputs.in_body {m l} {Γ : Context m} {w z a alpha f B R D S Base j t Q E n q x y out direct : Fin m}
    {cv : Fin 6 → Fin m} (h : Inputs Γ w z a alpha f B R D S Base j t Q E n q x y out direct cv)
    (F : Formula (m+l)) :
    Inputs (Context.add F (raisedContext l Γ)) (old l w) (old l z) (old l a) (old l alpha) (old l f)
      (old l B) (old l R) (old l D) (old l S) (old l Base) (old l j) (old l t) (old l Q) (old l E)
      (old l n) (old l q) (old l x) (old l y) (old l out) (old l direct) (fun i => old l (cv i)) :=
  ⟨HornBinderRules.zf_body l h.zf F,
    of_eq (frame_rename w z f B R D S Base j t Q E (old l)) (HornBinderRules.under_body l h.frame F),
    of_eq (ForcingConditionRebind.data_rename w a f alpha j n q cv (old l))
      (HornBinderRules.under_body l h.compiler F),
    of_eq (path_rename w z a alpha f B R D S E x y out direct cv (old l))
      (HornBinderRules.under_body l h.path F)⟩

private theorem Inputs.opened_field {m} {Γ : Context m}
    {w z a alpha f B R D S Base j t Q E n q x y out direct : Fin m} {cv : Fin 6 → Fin m}
    (h : Inputs Γ w z a alpha f B R D S Base j t Q E n q x y out direct cv)
    (bound : Bool) (i : Fin m) (hi : Derives Γ (SyntaxVariableSyntax.code bound w i y)) :
    Derives Γ ((Formula.mem i (SyntaxTermSyntax.limit bound alpha f)).conj
      (field w (SyntaxIndexMapSyntax.selectMap bound D S) i out)) := by
  have hq := Derives.conjL (.conjR h.path)
  have lists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w D S alpha f z B y out hq)
  exact .impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf bound w D S alpha f z B y out i
    (.conjL h.frame) lists hi)) hq

private theorem Inputs.direct_field {m} {Γ : Context m}
    {w z a alpha f B R D S Base j t Q E n q x y out direct : Fin m} {cv : Fin 6 → Fin m}
    (h : Inputs Γ w z a alpha f B R D S Base j t Q E n q x y out direct cv)
    (bound : Bool) (i : Fin m) (hi : Derives Γ (SyntaxVariableSyntax.code bound w i x)) :
    Derives Γ ((Formula.mem i (SyntaxTermSyntax.limit bound a f)).conj
      (field w (SyntaxIndexMapSyntax.selectMap bound R E) i direct)) := by
  have hq := Derives.conjR (.conjR h.path)
  have lists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w R E a f z B x direct hq)
  exact .impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf bound w R E a f z B x direct i
    (.conjL h.frame) lists hi)) hq

private theorem bound_at {m} {Γ : Context m} {w z a alpha f B R D S Base j t Q E n q x y out direct : Fin m}
    {cv : Fin 6 → Fin m} (h : Inputs Γ w z a alpha f B R D S Base j t Q E n q x y out direct cv)
    (i I : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code true w i x))
    (hI : Derives Γ (successor I i)) : Derives Γ (.equal out direct) := by
  have hw := Derives.conjL h.frame
  have hi := SyntaxVariableDecode.index_natural true w i x hx
  have hOld := h.direct_field true i hx
  have hY := Derives.impE (.conjL (ForcingRebindTerms.from_data h.zf true w a f alpha j n q x y i I cv
    hw h.compiler hx (.conjL hOld) hI)) (.conjL h.path)
  have hNew := h.opened_field true I hY
  have hTerm := Derives.conjL (.conjR (.conjR h.frame))
  have hCons := Derives.conjL (.conjR (.conjR (.conjR h.frame)))
  have lists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w R E a f z B x direct
    (.conjR (.conjR h.path)))
  have hR := Derives.conjL (.conjL (.conjR (.conjR (.conjL lists))))
  have hTail := StructuralListFieldCons.successor_forward h.zf w t R D i I out hw
    (SyntaxTerms.range h.zf w z B t hw hTerm) hR hi hI hCons (.conjR hNew)
  exact StructuralListFieldValues.unique h.zf w R i out direct hw hi hTail (.conjR hOld)

private theorem field_away {m} {Γ : Context m} (w L j t E i v : Fin m)
    (hi : Derives Γ (Formula.equal i j).neg)
    (h : Derives Γ (ForcingReflexiveImages.fieldResult w L j t E i v))
    (hv : Derives Γ (field w E i v)) : Derives Γ (field w L i v) := by
  apply Derives.disjE (.impE (.conjL h) hv)
  · exact .botE (.impE (add hi _) (.conjL (.hyp (Or.inl rfl))))
  · exact .conjR (.hyp (Or.inl rfl))

private theorem free_at {m} {Γ : Context m} {w z a alpha f B R D S Base j t Q E n q x y out direct : Fin m}
    {cv : Fin 6 → Fin m} (h : Inputs Γ w z a alpha f B R D S Base j t Q E n q x y out direct cv)
    (i : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code false w i x)) :
    Derives Γ (.equal out direct) := by
  have hw := Derives.conjL h.frame
  have hOld := h.direct_field false i hx
  have hi := Derives.conjL hOld
  have ht : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  have hY := Derives.impE (.conjL (ForcingRebindTerms.from_data h.zf false w a f alpha j n q x y i i cv
    hw h.compiler hx hi ht)) (.conjL h.path)
  have updates := Derives.conjR (.conjR (.conjR (.conjR h.frame)))
  have oldField := ForcingReflexiveImages.field_iff w f z B Base j t E i direct (.conjR updates) hi
  apply Derives.disjE hY
  · let C := (Formula.equal i j).conj (.equal y (cv 1))
    have hC : Derives (Context.add C Γ) C := .hyp (Or.inl rfl)
    have hz := Derives.conjL (.conjR h.frame)
    have head := Derives.conjL h.compiler
    have ez := OmegaUniversal.empty_unique (cv 0) z (ZFContext.arithmetic h.zf).base.extensionality
      (.conjL head) hz
    have hCode := SyntaxVariableImagePoint.code_subst_index true w (cv 0) (cv 1) z ez (.conjL (.conjR head))
    have hy := Derives.impE (add (.conjR (AbstractBinderRename.code_iff_equal h.zf true w z
      (cv 1) y hw hCode)) C) (.conjR hC)
    have hRaw := add (.conjL (.conjR h.path)) C
    have lists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w D S alpha f z B y out hRaw)
    have hAt := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field (ZFContext.add h.zf C) true
      w D S alpha f z B y out z (add hw C) lists hy)) hRaw
    have boundList := Derives.conjL (.conjL (SyntaxCodedMixedTermTyping.input_of_substituted
      w R E a f z B x direct (.conjR (.conjR h.path))))
    have hR := Derives.conjL (.conjL (.conjR (.conjR boundList)))
    have hTerm := Derives.conjL (.conjR (.conjR h.frame))
    have hCons := Derives.conjL (.conjR (.conjR (.conjR h.frame)))
    have ey := StructuralListFieldCons.zero_point (ZFContext.add h.zf C) w t R D z out
      (add hw C) (add (SyntaxTerms.range h.zf w z B t hw hTerm) C) (add hR C) (add hCons C)
      (add hz C) (.conjR hAt)
    have eo : Derives (Context.add C Γ) (.equal direct t) := by
      apply Derives.disjE (.impE (add (.conjL oldField) C) (add (.conjR hOld) C))
      · exact .conjR (.hyp (Or.inl rfl))
      · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add (.conjL hC) _))
    exact eq_trans ey (eq_symm eo)
  · let C := (Formula.equal i j).neg.conj (SyntaxVariableSyntax.code false w i y)
    have hC : Derives (Context.add C Γ) C := .hyp (Or.inl rfl)
    have hRaw := add (.conjL (.conjR h.path)) C
    have lists := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w D S alpha f z B y out hRaw)
    have hAt := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field (ZFContext.add h.zf C) false
      w D S alpha f z B y out i (add hw C) lists (.conjR hC))) hRaw
    have hn := Derives.conjL hC
    have hS := ForcingReflexiveImages.field_iff w f z B Base j Q S i out (add (.conjL updates) C) (add hi C)
    have oi := SyntaxVariableDecode.index_natural false w i x hx
    exact StructuralListFieldValues.unique (ZFContext.add h.zf C) w Base i out direct (add hw C) (add oi C)
      (field_away w Base j Q S i out hn hS (.conjR hAt))
      (field_away w Base j t E i direct hn (add oldField C) (add (.conjR hOld) C))

private theorem term {m} {Γ : Context m} {w z a alpha f B R D S Base j t Q E n q x y out direct : Fin m}
    {cv : Fin 6 → Fin m} (h : Inputs Γ w z a alpha f B R D S Base j t Q E n q x y out direct cv) :
    Derives Γ (.equal out direct) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w R E a f z B x direct (.conjR (.conjR h.path))
  apply Derives.disjE (.conjR ht)
  · let F := SyntaxTermSyntax.branchWitness true w a x
    let G := SyntaxTermSyntax.branch true w a x
    have hG : Derives (Context.add G Γ) G := .hyp (Or.inl rfl)
    apply Derives.exE (p := F) hG
    have hA : Derives (Context.add F (raisedContext 1 (Context.add G Γ))) F := .hyp (Or.inl rfl)
    have h1 := (⟨ZFContext.add h.zf G, add h.frame G, add h.compiler G, add h.path G⟩ :
      Inputs (Context.add G Γ) w z a alpha f B R D S Base j t Q E n q x y out direct cv).in_body F
    let J := successor (Fin.last (m+1)) (Fin.last m).castSucc
    have hs := InsertExistence.exists_insert (Fin.last m) (Fin.last m)
      (ZFContext.arithmetic h1.zf).base.pairing (ZFContext.arithmetic h1.zf).base.union
    apply Derives.exE (p := J) hs
    exact bound_at (h1.in_body J) (Fin.last m).castSucc (Fin.last (m+1))
      (of_eq (SyntaxVariableSyntax.code_rename true w.castSucc (Fin.last m) x.castSucc Fin.castSucc)
        (under (.conjR hA) J)) (.hyp (Or.inl rfl))
  · let F := SyntaxTermSyntax.branchWitness false w f x
    let G := SyntaxTermSyntax.branch false w f x
    have hG : Derives (Context.add G Γ) G := .hyp (Or.inl rfl)
    apply Derives.exE (p := F) hG
    have hA : Derives (Context.add F (raisedContext 1 (Context.add G Γ))) F := .hyp (Or.inl rfl)
    have h1 := (⟨ZFContext.add h.zf G, add h.frame G, add h.compiler G, add h.path G⟩ :
      Inputs (Context.add G Γ) w z a alpha f B R D S Base j t Q E n q x y out direct cv).in_body F
    exact free_at h1 (Fin.last m) (.conjR hA)


open SyntaxMixedFormulaJudgmentSyntax (substituted_rename)
local notation "query" => SyntaxMixedFormulaJudgmentSyntax.substituted

private def executions {m} (w z a alpha f B R D S E n q Y O : Fin m) : Formula m :=
  (query w D S alpha f z B q Y).conj (query w R E a f z B n O)

private theorem executions_rename {m l} (w z a alpha f B R D S E n q Y O : Fin m) (ρ : Fin m → Fin l) :
    (executions w z a alpha f B R D S E n q Y O).rename ρ = executions (ρ w) (ρ z) (ρ a) (ρ alpha) (ρ f) (ρ B) (ρ R) (ρ D) (ρ S) (ρ E) (ρ n) (ρ q)
      (ρ Y) (ρ O) := by
  simp only [executions, Formula.rename, substituted_rename]

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

attribute [local irreducible] SyntaxCodedMixedTermSyntax.substituted in
private theorem diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a alpha f B R D S Base j t Q E n q I J IB IF : Fin m) (cv : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z f B R D S Base j t Q E))
    (hc : Derives Γ (ForcingConditionRebind.data w a f alpha j n q cv))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF a f a f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four a a alpha z) (four f f f B)
      (four IB (cv 3) D R) (four IF (cv 5) S E)) := by
  let G := (substituted (old 5 w) (old 5 IB) (old 5 IF) (old 5 a) (old 5 f) (old 5 a) (old 5 f)
    (slot 5 0) (slot 5 1)).conj
    ((substituted (old 5 w) (old 5 (cv 3)) (old 5 (cv 5)) (old 5 a) (old 5 f) (old 5 alpha) (old 5 f)
      (slot 5 1) (slot 5 2)).conj
      ((substituted (old 5 w) (old 5 D) (old 5 S) (old 5 alpha) (old 5 f) (old 5 z) (old 5 B)
        (slot 5 2) (slot 5 3)).conj
        (substituted (old 5 w) (old 5 R) (old 5 E) (old 5 a) (old 5 f) (old 5 z) (old 5 B)
          (slot 5 0) (slot 5 4))))
  change Derives Γ (OriginalUniversalBlock.allMany 5 (G.imp (.equal (slot 5 3) (slot 5 4))))
  refine OriginalUniversalBlock.intro_many 5 _ (.impI ?_)
  let Δ := Context.add G (raisedContext 5 Γ)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ G
  have hf5 := of_eq (frame_rename w z f B R D S Base j t Q E (old 5)) (HornBinderRules.under_body 5 hf G)
  have hc5 := of_eq (ForcingConditionRebind.data_rename w a f alpha j n q cv (old 5))
    (HornBinderRules.under_body 5 hc G)
  have hI5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 5)) (HornBinderRules.under_body 5 hI G)
  have hJ5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 5)) (HornBinderRules.under_body 5 hJ G)
  have he5 := of_eq (IndexTermImageCodeSyntax.environment_rename w I J IB IF a f a f (old 5))
    (HornBinderRules.under_body 5 he G)
  have hId := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 a) (old 5 f)
    (old 5 I) (old 5 J) (old 5 IB) (old 5 IF) (slot 5 0) (slot 5 1) (.conjL hf5) hI5 hJ5 he5 (.conjL hG)
  have first := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 (cv 3)) (old 5 (cv 5))
    (old 5 a) (old 5 f) (old 5 alpha) (old 5 f) (slot 5 1) (slot 5 2) (slot 5 0)
    (eq_symm hId) (.conjL (.conjR hG))
  have h : Inputs Δ (old 5 w) (old 5 z) (old 5 a) (old 5 alpha) (old 5 f) (old 5 B)
      (old 5 R) (old 5 D) (old 5 S) (old 5 Base) (old 5 j) (old 5 t) (old 5 Q) (old 5 E)
      (old 5 n) (old 5 q) (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (cv i)) :=
    ⟨hZ5, hf5, hc5, .conjI first (.conjR (.conjR hG))⟩
  exact term h

private theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a alpha f B R D S Base j t Q E n q Y O I J : Fin m) (cv : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z f B R D S Base j t Q E))
    (hc : Derives Γ (ForcingConditionRebind.data w a f alpha j n q cv))
    (hq : Derives Γ (executions w z a alpha f B R D S E n q Y O))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J)) : Derives Γ (.equal Y O) := by
  let G := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 a) (old 2 f) (old 2 a) (old 2 f)
  let Δ := Context.add G (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 G _ (IndexTermImageEnvironment.exists_environment hZ w I J a f a f
    (.conjL hf) (SyntaxIdentityCode.map_code w a I hI) (SyntaxIdentityCode.map_code w f J hJ))
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ G
  have hf2 := of_eq (frame_rename w z f B R D S Base j t Q E (old 2)) (HornBinderRules.under_body 2 hf G)
  have hc2 := of_eq (ForcingConditionRebind.data_rename w a f alpha j n q cv (old 2))
    (HornBinderRules.under_body 2 hc G)
  have hq2 := of_eq (executions_rename w z a alpha f B R D S E n q Y O (old 2))
    (HornBinderRules.under_body 2 hq G)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 2)) (HornBinderRules.under_body 2 hI G)
  have hJ2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 2)) (HornBinderRules.under_body 2 hJ G)
  have hChild := Derives.conjR (.conjR (.conjR hc2))
  have hw := Derives.conjL hf2
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ2 (old 2 w) (old 2 (cv 3)) (old 2 (cv 5))
    (old 2 a) (old 2 f) (old 2 alpha) (old 2 f) (old 2 n) (old 2 q) hw hChild
  have hId := SyntaxIdentityInduction.reflexive hZ2 (old 2 w) (old 2 I) (old 2 J)
    (old 2 a) (old 2 f) (old 2 n) hw hI2 hJ2 hType
  have self := Derives.impE (.conjL (IndexFormulaRenameBridge.rename_iff hZ2 (old 2 w) (old 2 I) (old 2 J)
    (slot 2 0) (slot 2 1) (old 2 a) (old 2 f) (old 2 a) (old 2 f) (old 2 n) (old 2 n) hw hG)) hId
  have hd := diagram hZ2 (old 2 w) (old 2 z) (old 2 a) (old 2 alpha) (old 2 f) (old 2 B) (old 2 R) (old 2 D) (old 2 S) (old 2 Base) (old 2 j) (old
    2 t) (old 2 Q) (old 2 E) (old 2 n) (old 2 q)
    (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (fun i => old 2 (cv i)) hf2 hc2 hI2 hJ2 hG
  exact ForcingFormulaInduction.cancel hZ2 (old 2 w) (four (old 2 a) (old 2 a) (old 2 alpha) (old 2 z))
    (four (old 2 f) (old 2 f) (old 2 f) (old 2 B)) (four (slot 2 0) (old 2 (cv 3)) (old 2 D) (old 2 R))
    (four (slot 2 1) (old 2 (cv 5)) (old 2 S) (old 2 E)) (old 2 n) (old 2 n) (old 2 q)
    (old 2 Y) (old 2 O) hw hd self hChild (.conjL hq2) (.conjR hq2)

private theorem at_rebind {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a alpha f B R D S Base j t Q E n q Y O : Fin m) (cv : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z f B R D S Base j t Q E))
    (hc : Derives Γ (ForcingConditionRebind.data w a f alpha j n q cv))
    (hq : Derives Γ (executions w z a alpha f B R D S E n q Y O)) : Derives Γ (.equal Y O) := by
  have hw := Derives.conjL hf
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (cv 3) (cv 5) a f alpha f n q hw
    (.conjR (.conjR (.conjR hc)))
  have guards := Derives.conjR (FormulaCodeProperties.guards w n a f hType)
  let I := SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add I (Context.image Formula.raise Γ)
  apply Derives.exE (p := I) (SyntaxIdentityCode.exists_code hZ w a hw (.conjL guards))
  have hI : Derives Δ I := .hyp (Or.inl rfl)
  let J := SyntaxIdentityMapSyntax.identityCode (old 2 w) (old 2 f) (Fin.last (m+1))
  let Ξ := Context.add J (Context.image Formula.raise Δ)
  apply Derives.exE (p := J) (SyntaxIdentityCode.exists_code (ZFContext.under hZ I) w.castSucc f.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw I)) (under (.conjR guards) I))
  have hJ : Derives Ξ J := .hyp (Or.inl rfl)
  have hF : Derives Ξ (frame (old 2 w) (old 2 z) (old 2 f) (old 2 B) (old 2 R) (old 2 D)
      (old 2 S) (old 2 Base) (old 2 j) (old 2 t) (old 2 Q) (old 2 E)) :=
    of_eq (by simp only [Formula.raise, frame_rename]; rfl) (under (under hf I) J)
  have hC : Derives Ξ (ForcingConditionRebind.data (old 2 w) (old 2 a) (old 2 f) (old 2 alpha)
      (old 2 j) (old 2 n) (old 2 q) (fun i => old 2 (cv i))) :=
    of_eq (by simp only [Formula.raise, ForcingConditionRebind.data_rename]; rfl) (under (under hc I) J)
  have hQ : Derives Ξ (executions (old 2 w) (old 2 z) (old 2 a) (old 2 alpha) (old 2 f) (old 2 B)
      (old 2 R) (old 2 D) (old 2 S) (old 2 E) (old 2 n) (old 2 q) (old 2 Y) (old 2 O)) :=
    of_eq (by simp only [Formula.raise, executions_rename]; rfl) (under (under hq I) J)
  exact at_codes (ZFContext.under (ZFContext.under hZ I) J) (old 2 w) (old 2 z) (old 2 a) (old 2 alpha) (old 2 f) (old 2 B) (old 2 R) (old 2 D)
    (old 2 S) (old 2 Base) (old 2 j) (old 2 t) (old 2 Q) (old 2 E) (old 2 n) (old 2 q) (old 2 Y) (old 2 O)
    (Fin.last m).castSucc (Fin.last (m+1)) (fun i => old 2 (cv i)) hF hC hQ
    (of_eq (by simp only [I, Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename]; rfl) (under hI J)) hJ

private theorem operand {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a alpha f B R D S Base j t Q E n q Y O : Fin m)
    (hf : Derives Γ (frame w z f B R D S Base j t Q E))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f alpha j n q))
    (hq : Derives Γ (executions w z a alpha f B R D S E n q Y O)) : Derives Γ (.equal Y O) := by
  let G := ForcingConditionRebind.data (old 6 w) (old 6 a) (old 6 f) (old 6 alpha)
    (old 6 j) (old 6 n) (old 6 q) (slot 6)
  let Δ := Context.add G (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 G _ hc
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  exact at_rebind (HornBinderRules.zf_body 6 hZ G) (old 6 w) (old 6 z) (old 6 a) (old 6 alpha) (old 6 f) (old 6 B) (old 6 R) (old 6 D) (old 6 S)
    (old 6 Base) (old 6 j) (old 6 t) (old 6 Q) (old 6 E) (old 6 n) (old 6 q) (old 6 Y) (old 6 O) (slot 6)
    (of_eq (frame_rename w z f B R D S Base j t Q E (old 6)) (HornBinderRules.under_body 6 hf G)) hG
    (of_eq (executions_rename w z a alpha f B R D S E n q Y O (old 6)) (HornBinderRules.under_body 6 hq G))


open SyntaxLogicalSyntax (binaryCode binaryCode_rename)

/-- The literal negative tail is the implication from the original child
at the freshly selected condition to the original falsum. -/
theorem compare {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a alpha f B R D S Base j t Q E N Rebound Bot SourceTail Y O F Tail : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxTermSyntax.term w z B t))
    (hCons : Derives Γ (StructuralListSyntax.consCode w t R D))
    (hNew : Derives Γ (ForcingReflexiveImages.replacement w f z B Base j Q S))
    (hOld : Derives Γ (ForcingReflexiveImages.replacement w f z B Base j t E))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f alpha j N Rebound))
    (hSrc : Derives Γ (binaryCode 2 w Rebound Bot SourceTail))
    (hBot : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 Bot))
    (hRaw : Derives Γ (query w D S alpha f z B SourceTail Y))
    (hOldQuery : Derives Γ (query w R E a f z B N O))
    (hFalse : Derives Γ (SyntaxNodeSyntax.constructor 0 0 w Fin.elim0 F))
    (hTail : Derives Γ (binaryCode 2 w O F Tail)) : Derives Γ (.equal Y Tail) := by
  have outputs := ForcingFormulaDiagram.binary_output hZ 2 w D S alpha f z B SourceTail Rebound Bot Y hw hSrc hRaw
  let G := ForcingFormulaDiagram.binaryBody 2 w D S alpha f z B Rebound Bot Y
  let Δ := Context.add G (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 G _ outputs
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ G
  have hf : Derives Γ (frame w z f B R D S Base j t Q E) :=
    .conjI hw (.conjI hz (.conjI ht (.conjI hCons (.conjI hNew hOld))))
  have hf2 := of_eq (frame_rename w z f B R D S Base j t Q E (old 2)) (HornBinderRules.under_body 2 hf G)
  have hc2 := of_eq (ForcingConditionRebind.compiled_rename w a f alpha j N Rebound (old 2))
    (HornBinderRules.under_body 2 hc G)
  have hOldQuery2 := of_eq (substituted_rename w R E a f z B N O (old 2))
    (HornBinderRules.under_body 2 hOldQuery G)
  have eqOperand := operand hZ2 (old 2 w) (old 2 z) (old 2 a) (old 2 alpha) (old 2 f) (old 2 B) (old 2 R) (old 2 D) (old 2 S) (old 2 Base) (old 2
    j) (old 2 t) (old 2 Q) (old 2 E) (old 2 N) (old 2 Rebound)
    (slot 2 0) (old 2 O) hf2 hc2 (.conjI (.conjL (.conjR hG)) hOldQuery2)
  have hBot2 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (old 2 w) Fin.elim0 (old 2 Bot)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map])
      (HornBinderRules.under_body 2 hBot G)
  have hFalse2 : Derives Δ (SyntaxNodeSyntax.constructor 0 0 (old 2 w) Fin.elim0 (old 2 F)) :=
    of_eq (by simp only [SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.zero_map])
      (HornBinderRules.under_body 2 hFalse G)
  have hw2 := Derives.conjL hf2
  have eqBottom := SyntaxMixedFormulaNullary.unique hZ2 false (old 2 w) (old 2 D) (old 2 S)
    (old 2 alpha) (old 2 f) (old 2 z) (old 2 B) (old 2 Bot) (slot 2 1) hw2 hBot2 (.conjR (.conjR hG))
  have eqFalse := SyntaxConstructors.unique hZ2 0 0 (old 2 w) Fin.elim0 (old 2 Bot) (old 2 F) hw2 hBot2 hFalse2
  have eF := eq_trans eqBottom eqFalse
  let L := binaryCode 2 (old 2 w).castSucc (Fin.last (m+2)) (slot 2 1).castSucc (old 2 Y).castSucc
  have left : Derives Δ (binaryCode 2 (old 2 w) (old 2 O) (slot 2 1) (old 2 Y)) :=
    of_eq (by simp only [L, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst L eqOperand (of_eq (by simp only [L, Formula.instantiate, binaryCode_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL hG)))
  let H := binaryCode 2 (old 2 w).castSucc (old 2 O).castSucc (Fin.last (m+2)) (old 2 Y).castSucc
  have whole : Derives Δ (binaryCode 2 (old 2 w) (old 2 O) (old 2 F) (old 2 Y)) :=
    of_eq (by simp only [H, Formula.instantiate, binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst H eF (of_eq (by simp only [H, Formula.instantiate, binaryCode_rename,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) left))
  have tail2 := of_eq (binaryCode_rename 2 w O F Tail (old 2)) (HornBinderRules.under_body 2 hTail G)
  exact SyntaxLogicalFields.binary_unique hZ2 2 (old 2 w) (old 2 O) (old 2 F) (old 2 Y) (old 2 Tail)
    hw2 whole tail2

end PPAC.Migration.ForcingRawNegTail
