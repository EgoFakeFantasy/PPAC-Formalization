import PPAC.Migration.ForcingRebindTerms
import PPAC.Migration.Internal.OriginalBinderStepSyntax

/-! Original coded mixed substitution commutes with an actual binder lift,
for arbitrary target bound scope. Unlike the empty-scope closed-image case,
the output is the ORIGINAL bound-shift/free-identity rename. Reuse existing
binder fields, source rename and internal variable decoding; no new kernel. -/
namespace PPAC.Migration.ForcingMixedTermLift
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private structure Inputs {m} (Γ : Context m) (w R S a b c d A C K H U V r s z n x q X Y : Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  omega : Derives Γ (omega w)
  lift : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)
  sourceShift : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w a A r)
  sourceIdentity : Derives Γ (SyntaxIdentityMapSyntax.identityMap w b s)
  shift : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)
  identity : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V)
  head : Derives Γ (SyntaxMixedImageHead.head w C d z n)
  old : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x q)
  raised : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b A b x X)

private theorem Inputs.add {m} {Γ : Context m} {w R S a b c d A C K H U V r s z n x q X Y : Fin m} (h : Inputs Γ w R S a b c d A C K H U V r s z n x q X Y) (E : Formula m) :
    Inputs (Context.add E Γ) w R S a b c d A C K H U V r s z n x q X Y := {
  zf := ZFContext.add h.zf E
  omega := SourceLogic.add h.omega E
  lift := SourceLogic.add h.lift E
  sourceShift := SourceLogic.add h.sourceShift E
  sourceIdentity := SourceLogic.add h.sourceIdentity E
  shift := SourceLogic.add h.shift E
  identity := SourceLogic.add h.identity E
  head := SourceLogic.add h.head E
  old := SourceLogic.add h.old E
  raised := SourceLogic.add h.raised E
}

private theorem Inputs.under {m} {Γ : Context m} {w R S a b c d A C K H U V r s z n x q X Y : Fin m} (h : Inputs Γ w R S a b c d A C K H U V r s z n x q X Y) (E : Formula (m+1)) :
    Inputs (Context.add E (Context.image Formula.raise Γ)) w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc U.castSucc V.castSucc r.castSucc s.castSucc z.castSucc n.castSucc x.castSucc q.castSucc X.castSucc Y.castSucc := {
  zf := ZFContext.under h.zf E
  omega := of_eq (omega_rename w Fin.castSucc) (SourceLogic.under h.omega E)
  lift := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c d A C K H Fin.castSucc) (SourceLogic.under h.lift E)
  sourceShift := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w a A r Fin.castSucc) (SourceLogic.under h.sourceShift E)
  sourceIdentity := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w b s Fin.castSucc) (SourceLogic.under h.sourceIdentity E)
  shift := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U Fin.castSucc) (SourceLogic.under h.shift E)
  identity := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w d V Fin.castSucc) (SourceLogic.under h.identity E)
  head := of_eq (SyntaxMixedImageHead.head_rename w C d z n Fin.castSucc) (SourceLogic.under h.head E)
  old := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w R S a b c d x q Fin.castSucc) (SourceLogic.under h.old E)
  raised := of_eq (SyntaxRenameTermSyntax.renamed_rename w r s a b A b x X Fin.castSucc) (SourceLogic.under h.raised E)
}

private theorem at_variable {m} {Γ : Context m} {w R S a b c d A C K H U V r s z n x q X Y : Fin m} (h : Inputs Γ w R S a b c d A C K H U V r s z n x q X Y)
    (bound : Bool) (i I : Fin m) (hx : Derives Γ (SyntaxVariableSyntax.code bound w i x))
    (hs : Derives Γ (ForcingOpenLift.step bound i I)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w K H A b C d X Y).iff
      (SyntaxRenameTermSyntax.renamed w U V c d C d q Y)) := by
  have hIn := SyntaxCodedMixedBinderTyping.input_lists w R S a b c d A C K H h.lift
  have hOut := SyntaxCodedMixedBinderTyping.output_lists w R S a b c d A C K H h.lift
  have hf := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf bound w R S a b c d x q i h.omega hIn hx)) h.old
  have ht := SyntaxCodedMixedTermTyping.source_type w R S a b c d x q h.old
  cases bound with
  | true =>
    have hc := Derives.impE (.conjL (AbstractBinderRename.bound_at h.zf w r s a b A x X i I h.omega h.sourceShift h.sourceIdentity ht hx hs)) h.raised
    have hm := SyntaxCodedMixedTermFields.at_field h.zf true w K H A b C d X Y I h.omega hOut hc
    have hb := SyntaxCodedMixedBinderFields.bound_iff h.zf w R S a b c d A C K H U V z n I i q Y
      h.omega h.lift h.shift h.identity h.head (.conjL hf) hs (.conjR hf)
    exact SyntaxTypeLocalTransfer.iff_trans hm hb
  | false =>
    have hc := Derives.impE (.conjL (AbstractBinderRename.free_at h.zf w r s a b A x X i h.omega h.sourceShift h.sourceIdentity ht hx)) h.raised
    have hm := SyntaxCodedMixedTermFields.at_field h.zf false w K H A b C d X Y i h.omega hOut hc
    have hb := SyntaxCodedMixedBinderFields.free_iff h.zf w R S a b c d A C K H U V z n i q Y
      h.omega h.lift h.shift h.identity h.head (.conjL hf) (.conjR hf)
    exact SyntaxTypeLocalTransfer.iff_trans hm hb

private theorem all_terms {m} {Γ : Context m} {w R S a b c d A C K H U V r s z n x q X Y : Fin m} (h : Inputs Γ w R S a b c d A C K H U V r s z n x q X Y) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w K H A b C d X Y).iff
      (SyntaxRenameTermSyntax.renamed w U V c d C d q Y)) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w R S a b c d x q h.old
  apply Derives.disjE (.conjR ht)
  · let E := SyntaxTermSyntax.branch true w a x
    let B := SyntaxTermSyntax.branchWitness true w a x
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w a x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have h1 := (h.add E).under B
    have ht1 := SyntaxCodedMixedTermTyping.source_type w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc q.castSucc h1.old
    have hin := StructuralListTraceOrder.member_member h1.zf w.castSucc (Fin.last m) a.castSucc h1.omega (.conjL (.conjL ht1)) (.conjL hB)
    let F := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)
    let Ξ := Context.add F (Context.image Formula.raise Δ)
    apply Derives.exE (p := F) (OriginalBinderStepSyntax.successor_exists w.castSucc (Fin.last m) h1.omega hin)
    have hF : Derives Ξ F := .hyp (Or.inl rfl)
    have hc : Derives Ξ (SyntaxVariableSyntax.code true w.castSucc.castSucc (Fin.last m).castSucc x.castSucc.castSucc) :=
      of_eq (SyntaxVariableSyntax.code_rename true w.castSucc (Fin.last m) x.castSucc Fin.castSucc) (under (.conjR hB) F)
    have ho := at_variable (h1.under F) true (Fin.last m).castSucc (Fin.last (m+1)) hc (.conjR hF)
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename, SyntaxRenameTermSyntax.renamed_rename]) ho
  · let E := SyntaxTermSyntax.branch false w b x
    let B := SyntaxTermSyntax.branchWitness false w b x
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w b x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs : Derives Δ (ForcingOpenLift.step false (Fin.last m) (Fin.last m)) := .impI (.hyp (Or.inl rfl))
    have ho := at_variable ((h.add E).under B) false (Fin.last m) (Fin.last m) (.conjR hB) hs
    exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename, SyntaxRenameTermSyntax.renamed_rename]) ho

/-- For arbitrary original target bound scope, lift the input using the real
source shift maps. The actual lifted mixed substitution is iff the ORIGINAL
rename of its old output. Head/index/successor witnesses are internal. -/
theorem natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w R S a b c d A C K H U V r s x q X Y : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H))
    (hr : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w a A r)) (hs : Derives Γ (SyntaxIdentityMapSyntax.identityMap w b s))
    (hU : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w c C U)) (hV : Derives Γ (SyntaxIdentityMapSyntax.identityMap w d V))
    (ho : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x q))
    (hx : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b A b x X)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w K H A b C d X Y).iff
      (SyntaxRenameTermSyntax.renamed w U V c d C d q Y)) := by
  have hIn := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c d A C K H hl
  have hctx := Derives.conjL (.conjR (.conjL (.conjL hIn)))
  let B := SyntaxMixedImageHead.head (old 2 w) (old 2 C) (old 2 d) (slot 2 0) (slot 2 1)
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ (SyntaxMixedImageHead.exists_head hZ w c C d hw (.conjL hctx) (.conjR hctx) (.conjR (.conjR hIn)))
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi : Inputs Δ (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 A) (old 2 C)
      (old 2 K) (old 2 H) (old 2 U) (old 2 V) (old 2 r) (old 2 s) (slot 2 0) (slot 2 1) (old 2 x) (old 2 q) (old 2 X) (old 2 Y) := {
    zf := HornBinderRules.zf_body 2 hZ B
    omega := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
    lift := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a b c d A C K H (old 2)) (HornBinderRules.under_body 2 hl B)
    sourceShift := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w a A r (old 2)) (HornBinderRules.under_body 2 hr B)
    sourceIdentity := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w b s (old 2)) (HornBinderRules.under_body 2 hs B)
    shift := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w c C U (old 2)) (HornBinderRules.under_body 2 hU B)
    identity := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w d V (old 2)) (HornBinderRules.under_body 2 hV B)
    head := hB
    old := of_eq (SyntaxCodedMixedTermSyntax.substituted_rename w R S a b c d x q (old 2)) (HornBinderRules.under_body 2 ho B)
    raised := of_eq (SyntaxRenameTermSyntax.renamed_rename w r s a b A b x X (old 2)) (HornBinderRules.under_body 2 hx B)
  }
  exact of_eq (by simp only [Formula.iff, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename, SyntaxRenameTermSyntax.renamed_rename]) (all_terms hi)

def input {m} (w R S a b c d A C K H U V r s x q X : Fin m) : Formula m :=
  (omega w).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).conj ((SyntaxFreeShiftSyntax.shiftMap w a A r).conj ((SyntaxIdentityMapSyntax.identityMap w b s).conj ((SyntaxFreeShiftSyntax.shiftMap w c C U).conj ((SyntaxIdentityMapSyntax.identityMap w d V).conj ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d x q).conj ((SyntaxRenameTermSyntax.renamed w r s a b A b x X))))))))

def sentence {m} (w R S a b c d A C K H U V r s x q X Y : Fin m) : Source.Sentence :=
  ((input w R S a b c d A C K H U V r s x q X).imp ((SyntaxCodedMixedTermSyntax.substituted w K H A b C d X Y).iff
    (SyntaxRenameTermSyntax.renamed w U V c d C d q Y))).close

theorem kernel_certificate {m} (w R S a b c d A C K H U V r s x q X Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w R S a b c d A C K H U V r s x q X Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input w R S a b c d A C K H U V r s x q X
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact natural (ZFContext.add (ZFContext.source_ZF m) E) w R S a b c d A C K H U V r s x q X Y
    (.conjL h)
    (.conjL (.conjR h))
    (.conjL (.conjR (.conjR h)))
    (.conjL (.conjR (.conjR (.conjR h))))
    (.conjL (.conjR (.conjR (.conjR (.conjR h)))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR h))))))
    (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h)))))))

end PPAC.Migration.ForcingMixedTermLift
