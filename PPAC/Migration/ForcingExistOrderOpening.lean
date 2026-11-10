import PPAC.Migration.ForcingExistChildCanonical
import PPAC.Migration.ForcingExistGuardsCode
import PPAC.Migration.ForcingRebindTerms
import PPAC.Migration.ForcingBinderFormula

/-! Pinned Force.ex uses R(r,q), obtained by the original condition rebind
of the reverse order guard. Here r remains BOUND: opening that rebind equals
the actual closed-name table with the condition slot overwritten by bvar0.
The existing term laws and full internal formula cancellation are consumed;
there is no new compiler, recursion, induction or proof kernel. -/
namespace PPAC.Migration.ForcingExistOrderOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open SyntaxMixedImageCodeSyntax (termLists termLists_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def frame {m} (w z a f T A c R S K H j head E : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((termLists w a f z T R S).conj
    ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A c K H).conj
      ((SyntaxMixedImageHead.head w c T z head).conj
        ((ForcingReflexiveImages.replacement w f c T S j head E).conj
          (termLists w a f c T R E))))))

theorem frame_rename {m l} (w z a f T A c R S K H j head E : Fin m) (r : Fin m → Fin l) :
    (frame w z a f T A c R S K H j head E).rename r =
      frame (r w) (r z) (r a) (r f) (r T) (r A) (r c) (r R) (r S) (r K) (r H) (r j) (r head) (r E) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, termLists_rename,
    SyntaxCodedMixedBinderSyntax.lifted_rename, SyntaxMixedImageHead.head_rename,
    ForcingReflexiveImages.replacement_rename]

def path {m} (w a f A c T R E K H x u y o : Fin m) (v : Fin 6 → Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w (v 3) (v 5) a f A f x u).conj
    ((SyntaxCodedMixedTermSyntax.substituted w K H A f c T u y).conj
      (SyntaxCodedMixedTermSyntax.substituted w R E a f c T x o))

theorem path_rename {m l} (w a f A c T R E K H x u y o : Fin m) (v : Fin 6 → Fin m) (r : Fin m → Fin l) :
    (path w a f A c T R E K H x u y o v).rename r =
      path (r w) (r a) (r f) (r A) (r c) (r T) (r R) (r E) (r K) (r H) (r x) (r u) (r y) (r o) (fun i => r (v i)) := by
  simp only [path, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

private structure Inputs {m} (Γ : Context m) (w z a f T A c R S K H j head E N Nraw x u y o : Fin m) (v : Fin 6 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hf : Derives Γ (frame w z a f T A c R S K H j head E)
  hc : Derives Γ (ForcingConditionRebind.data w a f A j N Nraw v)
  hp : Derives Γ (path w a f A c T R E K H x u y o v)

private theorem Inputs.add {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) (B : Formula m) :
    Inputs (Context.add B Γ) w z a f T A c R S K H j head E N Nraw x u y o v :=
  ⟨ZFContext.add h.zf B, SourceLogic.add h.hf B, SourceLogic.add h.hc B, SourceLogic.add h.hp B⟩

private theorem Inputs.in_body {m n} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) (B : Formula (m+n)) :
    Inputs (Context.add B (raisedContext n Γ)) (old n w) (old n z) (old n a) (old n f) (old n T) (old n A) (old n c) (old n R) (old n S) (old n K) (old n H) (old n j) (old n head) (old n E) (old n N) (old n Nraw) (old n x) (old n u) (old n y) (old n o) (fun i => old n (v i)) :=
  ⟨HornBinderRules.zf_body n h.zf B,
    of_eq (frame_rename w z a f T A c R S K H j head E (old n)) (HornBinderRules.under_body n h.hf B),
    of_eq (ForcingConditionRebind.data_rename w a f A j N Nraw v (old n)) (HornBinderRules.under_body n h.hc B),
    of_eq (path_rename w a f A c T R E K H x u y o v (old n)) (HornBinderRules.under_body n h.hp B)⟩

private theorem Inputs.hw {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (omega w) := .conjL h.hf
private theorem Inputs.zero {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (empty z) := .conjL (.conjR h.hf)
private theorem Inputs.closed {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (termLists w a f z T R S) := .conjL (.conjR (.conjR h.hf))
private theorem Inputs.lift {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A c K H) := .conjL (.conjR (.conjR (.conjR h.hf)))
private theorem Inputs.head {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (SyntaxMixedImageHead.head w c T z head) := .conjL (.conjR (.conjR (.conjR (.conjR h.hf))))
private theorem Inputs.replacement {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (ForcingReflexiveImages.replacement w f c T S j head E) := .conjL (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))
private theorem Inputs.canonical {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (termLists w a f c T R E) := .conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))
private theorem Inputs.first {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w (v 3) (v 5) a f A f x u) := .conjL h.hp
private theorem Inputs.second {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w K H A f c T u y) := .conjL (.conjR h.hp)
private theorem Inputs.direct {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R E a f c T x o) := .conjR (.conjR h.hp)

private theorem bound_at {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) (i I : Fin m)
    (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) (hs : Derives Γ (successor I i)) : Derives Γ (.equal y o) := by
  have hi := SyntaxTerms.member h.zf true w a f x i h.hw hx (SyntaxCodedMixedTermTyping.source_type _ _ _ _ _ _ _ _ _ h.direct)
  have hu := Derives.impE (.conjL (ForcingRebindTerms.from_data h.zf true w a f A j N Nraw x u i I v h.hw h.hc hx hi hs)) h.first
  have hy := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w K H A f c T u y I h.hw
    (SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h.lift) hu)) h.second
  have ho := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w R E a f c T x o i h.hw h.canonical hx)) h.direct
  have hOld := ForcingOpenLift.old_fields_from_lists h.zf true w z a f T A c R S K H i I o y h.hw h.zero h.closed h.lift hi (.conjR ho) hs
  exact Derives.impE (.conjL hOld) hy

private theorem bound_point {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) (i : Fin m)
    (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) : Derives Γ (.equal y o) := by
  let B := successor (Fin.last m) i.castSucc
  apply Derives.exE (p := B) (InsertExistence.exists_insert i i (ZFContext.arithmetic h.zf).base.pairing (ZFContext.arithmetic h.zf).base.union)
  exact bound_at (h.in_body B) i.castSucc (Fin.last m)
    (of_eq (SyntaxVariableSyntax.code_rename true w i x Fin.castSucc) (under hx B)) (.hyp (Or.inl rfl))

private theorem selected_point {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v)
    (hx : Derives Γ (SyntaxVariableSyntax.code false w j x)) : Derives Γ (.equal y o) := by
  have hj := SyntaxTerms.member h.zf false w a f x j h.hw hx (SyntaxCodedMixedTermTyping.source_type _ _ _ _ _ _ _ _ _ h.direct)
  have ht : Derives Γ (ForcingOpenLift.step false j j) := .impI (.hyp (Or.inl rfl))
  have hu := Derives.impE (.conjL (ForcingRebindTerms.from_data h.zf false w a f A j N Nraw x u j j v h.hw h.hc hx hj ht)) h.first
  have huEq : Derives Γ (.equal u (v 1)) := by
    apply Derives.disjE hu
    · exact .conjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.eqRefl j))
  have hzEq := OmegaUniversal.empty_unique (v 0) z (ZFContext.arithmetic h.zf).base.extensionality (.conjL (.conjL h.hc)) h.zero
  have hCode := SyntaxVariableImagePoint.code_subst_index true w (v 0) (v 1) z hzEq (.conjL (.conjR (.conjL h.hc)))
  have hu0 := Derives.impE (.conjR (AbstractBinderRename.code_iff_equal h.zf true w z (v 1) u h.hw hCode)) huEq
  have hy := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w K H A f c T u y z h.hw
    (SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h.lift) hu0)) h.second
  have hzero := ForcingOpenLift.zero_code_from_lists h.zf w z a f T A c R S K H y h.hw h.zero h.closed h.lift hy
  have hyHead := SyntaxVariables.unique h.zf true w z y head h.hw hzero (.conjL (.conjR h.head))
  have ho := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w R E a f c T x o j h.hw h.canonical hx)) h.direct
  have he := Derives.impE (.conjL (ForcingReflexiveImages.field_iff w f c T S j head E j o h.replacement hj)) (.conjR ho)
  have hoHead : Derives Γ (.equal o head) := by
    apply Derives.disjE he
    · exact .conjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (.eqRefl j))
  exact eq_trans hyHead (eq_symm hoHead)

private theorem away_point {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) (i : Fin m)
    (hx : Derives Γ (SyntaxVariableSyntax.code false w i x)) (hn : Derives Γ (Formula.equal i j).neg) : Derives Γ (.equal y o) := by
  have hi := SyntaxTerms.member h.zf false w a f x i h.hw hx (SyntaxCodedMixedTermTyping.source_type _ _ _ _ _ _ _ _ _ h.direct)
  have ht : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  have hu := Derives.impE (.conjL (ForcingRebindTerms.from_data h.zf false w a f A j N Nraw x u i i v h.hw h.hc hx hi ht)) h.first
  have huVar : Derives Γ (SyntaxVariableSyntax.code false w i u) := by
    apply Derives.disjE hu
    · exact .botE (.impE (add hn _) (.conjL (.hyp (Or.inl rfl))))
    · exact .conjR (.hyp (Or.inl rfl))
  have hy := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w K H A f c T u y i h.hw
    (SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h.lift) huVar)) h.second
  have ho := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w R E a f c T x o i h.hw h.canonical hx)) h.direct
  have hE := Derives.impE (.conjL (ForcingReflexiveImages.field_iff w f c T S j head E i o h.replacement hi)) (.conjR ho)
  have hS : Derives Γ (field w S i o) := by
    apply Derives.disjE hE
    · exact .botE (.impE (add hn _) (.conjL (.hyp (Or.inl rfl))))
    · exact .conjR (.hyp (Or.inl rfl))
  exact Derives.impE (.conjL (ForcingOpenLift.old_fields_from_lists h.zf false w z a f T A c R S K H i i o y
    h.hw h.zero h.closed h.lift hi hS ht)) hy

private theorem term_from_inputs {m} {Γ : Context m} {w z a f T A c R S K H j head E N Nraw x u y o : Fin m} {v : Fin 6 → Fin m}
    (h : Inputs Γ w z a f T A c R S K H j head E N Nraw x u y o v) : Derives Γ (.equal y o) := by
  have ht := SyntaxCodedMixedTermTyping.source_type _ _ _ _ _ _ _ _ _ h.direct
  apply Derives.disjE (.conjR ht)
  · let J := SyntaxTermSyntax.branch true w a x
    let B := SyntaxTermSyntax.branchWitness true w a x
    let Δ := Context.add B (Context.image Formula.raise (Context.add J Γ))
    apply SyntaxTermSyntax.eliminate_branch true w a x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact bound_point ((h.add J).in_body B) (Fin.last m) (.conjR hB)
  · let J := SyntaxTermSyntax.branch false w f x
    let B := SyntaxTermSyntax.branchWitness false w f x
    let Δ := Context.add B (Context.image Formula.raise (Context.add J Γ))
    apply SyntaxTermSyntax.eliminate_branch false w f x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have h1 := (h.add J).in_body B
    apply SourcePropositional.by_cases (.equal (Fin.last m) j.castSucc)
    · have hxj := SyntaxVariableImagePoint.code_subst_index false w.castSucc (Fin.last m) x.castSucc j.castSucc
        (.hyp (Or.inl rfl)) (add (.conjR hB) _)
      exact selected_point (h1.add _) hxj
    · exact away_point (h1.add _) (Fin.last m) (add (.conjR hB) _) (.hyp (Or.inl rfl))

theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H j head E N Nraw x u y o : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E))
    (hc : Derives Γ (ForcingConditionRebind.data w a f A j N Nraw v))
    (hp : Derives Γ (path w a f A c T R E K H x u y o v)) : Derives Γ (.equal y o) :=
  term_from_inputs ⟨hZ, hf, hc, hp⟩


private def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H j head E N Nraw I J IB IF : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E)) (hc : Derives Γ (ForcingConditionRebind.data w a f A j N Nraw v))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF a f a f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four a a A c) (four f f f T)
      (four IB (v 3) K R) (four IF (v 5) H E)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let G := (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 IB) (old 5 IF) (old 5 a) (old 5 f) (old 5 a) (old 5 f) (slot 5 0) (slot 5 1)).conj
    ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 (v 3)) (old 5 (v 5)) (old 5 a) (old 5 f) (old 5 A) (old 5 f) (slot 5 1) (slot 5 2)).conj
      ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 K) (old 5 H) (old 5 A) (old 5 f) (old 5 c) (old 5 T) (slot 5 2) (slot 5 3)).conj
        (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 R) (old 5 E) (old 5 a) (old 5 f) (old 5 c) (old 5 T) (slot 5 0) (slot 5 4))))
  let Δ := Context.add G (raisedContext 5 Γ)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hf5 := of_eq (frame_rename w z a f T A c R S K H j head E (old 5)) (HornBinderRules.under_body 5 hf G)
  have hc5 := of_eq (ForcingConditionRebind.data_rename w a f A j N Nraw v (old 5)) (HornBinderRules.under_body 5 hc G)
  have hI5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 5)) (HornBinderRules.under_body 5 hI G)
  have hJ5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 5)) (HornBinderRules.under_body 5 hJ G)
  have he5 := of_eq (IndexTermImageCodeSyntax.environment_rename w I J IB IF a f a f (old 5)) (HornBinderRules.under_body 5 he G)
  have hZ5 := HornBinderRules.zf_body 5 hZ G
  have hId := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 a) (old 5 f)
    (old 5 I) (old 5 J) (old 5 IB) (old 5 IF) (slot 5 0) (slot 5 1) (.conjL hf5) hI5 hJ5 he5 (.conjL hG)
  have hFirst := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 (v 3)) (old 5 (v 5))
    (old 5 a) (old 5 f) (old 5 A) (old 5 f) (slot 5 1) (slot 5 2) (slot 5 0) (eq_symm hId) (.conjL (.conjR hG))
  exact term hZ5 (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 c) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 j) (old 5 head) (old 5 E) (old 5 N) (old 5 Nraw) (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (v i))
    hf5 hc5 (.conjI hFirst (.conjI (.conjL (.conjR (.conjR hG))) (.conjR (.conjR (.conjR hG)))))

private theorem at_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H j head E N Nraw Y O I J IB IF : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E)) (hc : Derives Γ (ForcingConditionRebind.data w a f A j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y))
    (hDirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E a f c T N O))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF a f a f)) : Derives Γ (.equal Y O) := by
  have hw := Derives.conjL hf
  have hChild := Derives.conjR (Derives.conjR (Derives.conjR hc))
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (v 3) (v 5) a f A f N Nraw hw hChild
  have hId := SyntaxIdentityInduction.reflexive hZ w I J a f N hw hI hJ hType
  have hIdMixed := Derives.impE (.conjL (IndexFormulaRenameBridge.rename_iff hZ w I J IB IF a f a f N N hw he)) hId
  have hd := term_diagram hZ w z a f T A c R S K H j head E N Nraw I J IB IF v hf hc hI hJ he
  exact ForcingFormulaInduction.cancel hZ w (four a a A c) (four f f f T)
    (four IB (v 3) K R) (four IF (v 5) H E) N N Nraw Y O hw hd hIdMixed hChild hOpen hDirect

private theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H j head E N Nraw Y O I J : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E)) (hc : Derives Γ (ForcingConditionRebind.data w a f A j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y))
    (hDirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E a f c T N O))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J)) : Derives Γ (.equal Y O) := by
  let G := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 a) (old 2 f) (old 2 a) (old 2 f)
  let Δ := Context.add G (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 G _ (IndexTermImageEnvironment.exists_environment hZ w I J a f a f (.conjL hf)
    (SyntaxIdentityCode.map_code w a I hI) (SyntaxIdentityCode.map_code w f J hJ))
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  exact at_identity (HornBinderRules.zf_body 2 hZ G) (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 c) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 j) (old 2 head) (old 2 E) (old 2 N) (old 2 Nraw) (old 2 Y) (old 2 O) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (fun i => old 2 (v i))
    (of_eq (frame_rename w z a f T A c R S K H j head E (old 2)) (HornBinderRules.under_body 2 hf G))
    (of_eq (ForcingConditionRebind.data_rename w a f A j N Nraw v (old 2)) (HornBinderRules.under_body 2 hc G))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f c T Nraw Y (old 2)) (HornBinderRules.under_body 2 hOpen G))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R E a f c T N O (old 2)) (HornBinderRules.under_body 2 hDirect G))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w a I (old 2)) (HornBinderRules.under_body 2 hI G))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 2)) (HornBinderRules.under_body 2 hJ G)) hG

/-- All internal formula codes, with r still bound: actual rebind/open equals
actual canonical overwrite. Existing full formula induction, unchanged. -/
theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H j head E N Nraw Y O : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E)) (hc : Derives Γ (ForcingConditionRebind.data w a f A j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y))
    (hDirect : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E a f c T N O)) : Derives Γ (.equal Y O) := by
  have hw := Derives.conjL hf
  have hChild := Derives.conjR (Derives.conjR (Derives.conjR hc))
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (v 3) (v 5) a f A f N Nraw hw hChild
  have hCtx := Derives.conjR (FormulaCodeProperties.guards w N a f hType)
  let IBody := SyntaxIdentityMapSyntax.identityCode w.castSucc a.castSucc (Fin.last m)
  let Δ1 := Context.add IBody (Context.image Formula.raise Γ)
  apply Derives.exE (p := IBody) (SyntaxIdentityCode.exists_code hZ w a hw (.conjL hCtx))
  have hI : Derives Δ1 IBody := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ IBody
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw IBody)
  have hfNat1 : Derives Δ1 (.mem f.castSucc w.castSucc) := under (.conjR hCtx) IBody
  let JBody := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Δ2 := Context.add JBody (Context.image Formula.raise Δ1)
  apply Derives.exE (p := JBody) (SyntaxIdentityCode.exists_code hZ1 w.castSucc f.castSucc hw1 hfNat1)
  have hJ : Derives Δ2 JBody := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 JBody
  have hf2 : Derives Δ2 (frame (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 c) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 j) (old 2 head) (old 2 E)) := of_eq
    (by simp only [Formula.raise, frame_rename]; rfl) (under (under hf IBody) JBody)
  have hc2 : Derives Δ2 (ForcingConditionRebind.data (old 2 w) (old 2 a) (old 2 f) (old 2 A) (old 2 j) (old 2 N) (old 2 Nraw) (fun i => old 2 (v i))) :=
    of_eq (by simp only [Formula.raise, ForcingConditionRebind.data_rename]; rfl) (under (under hc IBody) JBody)
  have ho2 : Derives Δ2 (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 K) (old 2 H) (old 2 A) (old 2 f) (old 2 c) (old 2 T) (old 2 Nraw) (old 2 Y)) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (under (under hOpen IBody) JBody)
  have hd2 : Derives Δ2 (SyntaxMixedFormulaJudgmentSyntax.substituted (old 2 w) (old 2 R) (old 2 E) (old 2 a) (old 2 f) (old 2 c) (old 2 T) (old 2 N) (old 2 O)) :=
    of_eq (by simp only [Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (under (under hDirect IBody) JBody)
  have hI2 := of_eq (by simp only [IBody, Formula.raise, SyntaxIdentityMapSyntax.identityCode_rename]; rfl) (under hI JBody)
  exact at_codes hZ2 (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 c) (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 j) (old 2 head) (old 2 E) (old 2 N) (old 2 Nraw) (old 2 Y) (old 2 O) (Fin.last m).castSucc (Fin.last (m+1)) (fun i => old 2 (v i)) hf2 hc2 ho2 hd2 hI2 hJ

private theorem output_subst {m} {Γ : Context m} (w R S a b c d n q r : Fin m)
    (he : Derives Γ (.equal q r)) (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n r) := by
  let P := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq))

/-- Generate and erase the canonical candidate; return its query at the same
ACTUAL raw output, with all four identity witnesses object-generated. -/
theorem query {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H j head E N Nraw Y : Fin m) (v : Fin 6 → Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E)) (hc : Derives Γ (ForcingConditionRebind.data w a f A j N Nraw v))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E a f c T N Y) := by
  have hw := Derives.conjL hf
  have hChild := Derives.conjR (Derives.conjR (Derives.conjR hc))
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (v 3) (v 5) a f A f N Nraw hw hChild
  have hLists := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))
  let G := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc E.castSucc a.castSucc f.castSucc c.castSucc T.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w R E a f c T N hw (.conjI hType hLists))
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hf1 := of_eq (frame_rename w z a f T A c R S K H j head E Fin.castSucc) (under hf G)
  have hc1 := of_eq (ForcingConditionRebind.data_rename w a f A j N Nraw v Fin.castSucc) (under hc G)
  have ho1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f c T Nraw Y Fin.castSucc) (under hOpen G)
  have heq := formula (ZFContext.under hZ G) w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc c.castSucc R.castSucc S.castSucc K.castSucc H.castSucc j.castSucc head.castSucc E.castSucc N.castSucc Nraw.castSucc Y.castSucc (Fin.last m) (fun i => (v i).castSucc) hf1 hc1 ho1 hG
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R E a f c T N Y Fin.castSucc).symm
    (output_subst _ _ _ _ _ _ _ _ _ _ (eq_symm heq) hG)

/-- Consume and eliminate all SIX ORIGINAL rebind witnesses. -/
theorem from_compiled {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A c R S K H j head E N Nraw Y : Fin m) (hf : Derives Γ (frame w z a f T A c R S K H j head E))
    (hc : Derives Γ (ForcingConditionRebind.compiled w a f A j N Nraw))
    (hOpen : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E a f c T N Y) := by
  let G := ForcingConditionRebind.data (old 6 w) (old 6 a) (old 6 f) (old 6 A) (old 6 j) (old 6 N) (old 6 Nraw) (slot 6)
  let Δ := Context.add G (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 G _ hc
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have ho := query (HornBinderRules.zf_body 6 hZ G) (old 6 w) (old 6 z) (old 6 a) (old 6 f) (old 6 T) (old 6 A) (old 6 c) (old 6 R) (old 6 S) (old 6 K) (old 6 H) (old 6 j) (old 6 head) (old 6 E) (old 6 N) (old 6 Nraw) (old 6 Y) (slot 6)
    (of_eq (frame_rename w z a f T A c R S K H j head E (old 6)) (HornBinderRules.under_body 6 hf G)) hG
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f c T Nraw Y (old 6)) (HornBinderRules.under_body 6 hOpen G))
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R E a f c T N Y (old 6)).symm ho


private theorem canonical_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a f c T R E E1 N N1 Y Y1 : Fin m) (hw : Derives Γ (omega w))
    (he : Derives Γ (.equal E E1)) (hn : Derives Γ (.equal N N1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E a f c T N Y))
    (hz : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E1 a f c T N1 Y1)) : Derives Γ (.equal Y Y1) := by
  let F := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc (Fin.last m) a.castSucc f.castSucc c.castSucc T.castSucc N.castSucc Y.castSucc
  have hF : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E1 a f c T N Y) :=
    of_eq (by simp only [F, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst F he (of_eq (by simp only [F, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hy))
  let G := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc E1.castSucc a.castSucc f.castSucc c.castSucc T.castSucc (Fin.last m) Y.castSucc
  have hG : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R E1 a f c T N1 Y) :=
    of_eq (by simp only [G, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst G hn (of_eq (by simp only [G, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hF))
  exact SyntaxMixedFormulaOutputInduction.unique hZ w R E1 a f c T N1 Y Y1 hw hG hz

/-- Read the ORIGINAL three existential guard witnesses. This is definitionally
its existing body, not another compiler or a separately supplied source code. -/
private def guardRecord {k m} (Reln : Source.Formula (k+2)) (w a A f j Nraw : Fin m) (v : Fin 3 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w a f (v 0) (v 1)).conj
    ((ForcingGuardCode.compiled true (ForcingExistGuardsCode.reverseOrder Reln) w a f (v 1) (v 2)).conj
      (ForcingConditionRebind.compiled w a f A j (v 2) Nraw))
private theorem guardRecord_rename {k m l} (Reln : Source.Formula (k+2)) (w a A f j Nraw : Fin m) (v : Fin 3 → Fin m) (r : Fin m → Fin l) :
    (guardRecord Reln w a A f j Nraw v).rename r = guardRecord Reln (r w) (r a) (r A) (r f) (r j) (r Nraw) (fun i => r (v i)) := by
  simp only [guardRecord, Formula.rename, SyntaxMixedImageHead.head_rename, ForcingGuardCode.compiled_rename, ForcingConditionRebind.compiled_rename]

private theorem guard_source_equal {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w a A f j Nraw Nraw1 : Fin m) (v u : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hv : Derives Γ (guardRecord Reln w a A f j Nraw v))
    (hu : Derives Γ (guardRecord Reln w a A f j Nraw1 u)) : Derives Γ (.equal (v 2) (u 2)) := by
  have hz := OmegaUniversal.empty_unique (v 0) (u 0) (ZFContext.arithmetic hZ).base.extensionality (.conjL (.conjL hv)) (.conjL (.conjL hu))
  have hc := AbstractVariableIndex.code_index_subst true w (v 0) (u 0) (v 1) hz (.conjL (.conjR (.conjL hv)))
  have he := SyntaxVariables.unique hZ true w (u 0) (v 1) (u 1) hw hc (.conjL (.conjR (.conjL hu)))
  let G := ForcingGuardCode.compiled true (ForcingExistGuardsCode.reverseOrder Reln) w.castSucc a.castSucc f.castSucc (Fin.last m) (v 2).castSucc
  have hG : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.reverseOrder Reln) w a f (u 1) (v 2)) :=
    of_eq (by simp only [G, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst G he (of_eq (by simp only [G, Formula.instantiate, ForcingGuardCode.compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL (.conjR hv))))
  exact ForcingGuardCode.unique hZ true (ForcingExistGuardsCode.reverseOrder Reln) w a f (u 1) (v 2) (u 2) hw hG (.conjL (.conjR hu))

private theorem guard_at_records {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1 : Fin m) (v u : Fin 3 → Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E))
    (hg : Derives Γ (frame w z a f T A c R S1 K1 H1 j head E1))
    (hc : Derives Γ (guardRecord Reln w a A f j Nraw v))
    (hd : Derives Γ (guardRecord Reln w a A f j Nraw1 u))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K1 H1 A f c T Nraw1 Y1))
    (hp : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j p S))
    (hq : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j q S1)) : Derives Γ (.equal Y Y1) := by
  have hY := from_compiled hZ w z a f T A c R S K H j head E (v 2) Nraw Y hf (.conjR (.conjR hc)) hy
  have hY1 := from_compiled hZ w z a f T A c R S1 K1 H1 j head E1 (u 2) Nraw1 Y1 hg (.conjR (.conjR hd)) hy1
  have hN := guard_source_equal hZ Reln w a A f j Nraw Nraw1 v u (.conjL hf) hc hd
  have hE := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))
  have hE1 := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hg)))))
  have he := ForcingExistChildCanonical.overwrite hZ w f c T Base j p q S S1 head E E1 (.conjL hf) hp hq hE hE1
  exact canonical_equal hZ w a f c T R E E1 (v 2) (u 2) Y Y1 (.conjL hf) he hN hY hY1

/-- Consume BOTH complete ORIGINAL inner-order compilers. Their three outer
witnesses and both six-witness rebind executions are internally eliminated.
The actual R(r,q) output is independent of the old outer condition value. -/
theorem guard_compare {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Reln : Source.Formula (k+2))
    (w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1 : Fin m)
    (hf : Derives Γ (frame w z a f T A c R S K H j head E))
    (hg : Derives Γ (frame w z a f T A c R S1 K1 H1 j head E1))
    (hc : Derives Γ (ForcingExistGuardsCode.compiled Reln w a A f j Nraw))
    (hd : Derives Γ (ForcingExistGuardsCode.compiled Reln w a A f j Nraw1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K1 H1 A f c T Nraw1 Y1))
    (hp : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j p S))
    (hq : Derives Γ (ForcingReflexiveImages.replacement w f c T Base j q S1)) : Derives Γ (.equal Y Y1) := by
  let G := guardRecord Reln (old 3 w) (old 3 a) (old 3 A) (old 3 f) (old 3 j) (old 3 Nraw) (slot 3)
  let Δ := Context.add G (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 G _ (.conjR hc)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hd3 := of_eq (ForcingExistGuardsCode.compiled_rename Reln w a A f j Nraw1 (old 3)) (HornBinderRules.under_body 3 hd G)
  let B := guardRecord Reln (old 6 w) (old 6 a) (old 6 A) (old 6 f) (old 6 j) (old 6 Nraw1) (slot 3)
  let Ξ := Context.add B (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 B _ (.conjR hd3)
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hG6 : Derives Ξ (guardRecord Reln (old 6 w) (old 6 a) (old 6 A) (old 6 f) (old 6 j) (old 6 Nraw) (fun i => old 3 (slot 3 i))) :=
    of_eq (by simp only [G, guardRecord_rename]; rfl) (HornBinderRules.under_body 3 hG B)
  have hf6 := of_eq (by simp only [frame_rename]; rfl)
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hf G) B)
  have hg6 := of_eq (by simp only [frame_rename]; rfl)
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hg G) B)
  have hy6 := of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl)
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hy G) B)
  have hy16 := of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl)
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hy1 G) B)
  have hp6 := of_eq (by simp only [ForcingReflexiveImages.replacement_rename]; rfl)
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hp G) B)
  have hq6 := of_eq (by simp only [ForcingReflexiveImages.replacement_rename]; rfl)
    (HornBinderRules.under_body 3 (HornBinderRules.under_body 3 hq G) B)
  exact of_eq (by simp only [Formula.rename]; rfl)
    (guard_at_records (HornBinderRules.zf_body 3 (HornBinderRules.zf_body 3 hZ G) B) Reln (old 6 w) (old 6 z) (old 6 a) (old 6 f) (old 6 T) (old 6 A) (old 6 c) (old 6 R) (old 6 S) (old 6 K) (old 6 H) (old 6 j) (old 6 head) (old 6 E) (old 6 Nraw) (old 6 Y) (old 6 Base) (old 6 p) (old 6 q) (old 6 S1) (old 6 K1) (old 6 H1) (old 6 E1) (old 6 Nraw1) (old 6 Y1)
      (fun i => old 3 (slot 3 i)) (slot 3) hf6 hg6 hG6 hB hy6 hy16 hp6 hq6)


def input {k m} (Reln : Source.Formula (k+2)) (w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1 : Fin m) : Formula m :=
  (frame w z a f T A c R S K H j head E).conj ((frame w z a f T A c R S1 K1 H1 j head E1).conj ((ForcingExistGuardsCode.compiled Reln w a A f j Nraw).conj ((ForcingExistGuardsCode.compiled Reln w a A f j Nraw1).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f c T Nraw Y).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w K1 H1 A f c T Nraw1 Y1).conj ((ForcingReflexiveImages.replacement w f c T Base j p S).conj (ForcingReflexiveImages.replacement w f c T Base j q S1)))))))

def sentence {k m} (Reln : Source.Formula (k+2)) (w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1 : Fin m) : Source.Sentence :=
  ((input Reln w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1).imp (.equal Y Y1)).close

theorem kernel_certificate {k m} (Reln : Source.Formula (k+2)) (w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1 : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence Reln w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := input Reln w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact guard_compare (ZFContext.add (ZFContext.source_ZF m) G) Reln w z a f T A c R S K H j head E Nraw Y Base p q S1 K1 H1 E1 Nraw1 Y1
    (Derives.conjL (hG))
    (Derives.conjL (Derives.conjR (hG)))
    (Derives.conjL (Derives.conjR (Derives.conjR (hG))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hG)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG)))))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))))

end PPAC.Migration.ForcingExistOrderOpening
