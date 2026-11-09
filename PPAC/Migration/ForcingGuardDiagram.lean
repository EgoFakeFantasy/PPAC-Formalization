import PPAC.Migration.ForcingMemberGuardOpening
import PPAC.Migration.ForcingFormulaInduction

/-! Root diagram for the ACTUAL original one-bound guard compiler, lifted
opening and native InstantiateTop operation. Complete internal formula
cancellation is reused unchanged; there is no new recursion or evaluator. -/
namespace PPAC.Migration.ForcingGuardDiagram
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem four_map {m l} (a b c d : Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (four a b c d i)) = four (ρ a) (ρ b) (ρ c) (ρ d) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i

def input {m} (w mode z a f T A C R S K H P r s t B I V head : Fin m) : Formula m :=
  (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s).conj
    ((SyntaxNumeralSyntax.numeral 1 t).conj ((SyntaxVariableSyntax.code true w z head).conj
      ((SyntaxForestSyntax.forest 1 w (fun _ => head) B).conj
        ((ForcingAtomicCode.identityImages w A f I).conj (SyntaxForestSyntax.forest 1 w (fun _ => P) V)))))
theorem input_rename {m l} (w mode z a f T A C R S K H P r s t B I V head : Fin m) (ρ : Fin m → Fin l) :
    (input w mode z a f T A C R S K H P r s t B I V head).rename ρ = input (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ t) (ρ B) (ρ I) (ρ V) (ρ head) := by
  simp only [input, Formula.rename, ForcingMemberGuardOpening.frame_rename, SyntaxNumeralSyntax.numeral_rename,
    SyntaxVariableSyntax.code_rename, SyntaxForestSyntax.forest_rename, ForcingAtomicCode.identityImages_rename]

private def path {m} (w _mode z _a f T A C _R S K H _P r s t B I V _head n u v y o : Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w B I t f A f n u).conj
    ((SyntaxCodedMixedTermSyntax.substituted w K H A f C T u v).conj
      ((SyntaxCodedMixedTermSyntax.substituted w r s C T z T v y).conj
        (SyntaxCodedMixedTermSyntax.substituted w V S t f z T n o)))
private theorem path_rename {m l} (w mode z a f T A C R S K H P r s t B I V head n u v y o : Fin m) (ρ : Fin m → Fin l) :
    (path w mode z a f T A C R S K H P r s t B I V head n u v y o).rename ρ = path (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ t) (ρ B) (ρ I) (ρ V) (ρ head) (ρ n) (ρ u) (ρ v) (ρ y) (ρ o) := by
  simp only [path, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

private theorem variable_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w mode z a f T A C R S K H P r s t B I V head n u v y o i : Fin m)
    (hr : Derives Γ (input w mode z a f T A C R S K H P r s t B I V head)) (hp : Derives Γ (path w mode z a f T A C R S K H P r s t B I V head n u v y o))
    (hi : Derives Γ (Formula.mem i (SyntaxTermSyntax.limit bound t f)))
    (hc : Derives Γ (SyntaxVariableSyntax.code bound w i n)) : Derives Γ (.equal y o) := by
  have hf := Derives.conjL hr
  have hw := Derives.conjL hf
  have hz := Derives.conjL (.conjR (.conjR hf))
  have hfirst := Derives.conjL hp
  have hsecond := Derives.conjL (.conjR hp)
  have hthird := Derives.conjL (.conjR (.conjR hp))
  have hdirect := Derives.conjR (.conjR (.conjR hp))
  have hL0 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B I t f A f n u hfirst)
  have hLD := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V S t f z T n o hdirect)
  cases bound with
  | true =>
    have hbelow := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ 1 t i (.conjL (.conjR hr)))) hi
    have hzi : Derives Γ (empty i) := .disjE hbelow (.botE (.hyp (Or.inl rfl))) (.hyp (Or.inl rfl))
    have heq := OmegaUniversal.empty_unique i z (ZFContext.arithmetic hZ).base.extensionality hzi hz
    have hcode := SyntaxVariableImagePoint.code_subst_index true w i n z heq hc
    have hfield := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w B I t f A f n u z hw hL0 hcode)) hfirst
    have hu := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ 1 w (fun _ => head) B 0 z u hw (.conjL (.conjR (.conjR (.conjR hr)))) hz)) (.conjR hfield)
    have hhead := Derives.conjL (.conjR (.conjR hr))
    have hsecond' := SyntaxMixedFormulaAtomicSubst.term_source w K H A f C T u v head hu hsecond
    have hy := ForcingMemberGuardOpening.zero_image hZ w mode z a f T A C R S K H P r s head v y hf hhead hsecond' hthird
    have hfD := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w V S t f z T n o z hw hLD hcode)) hdirect
    have ho := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ 1 w (fun _ => P) V 0 z o hw (.conjR (.conjR (.conjR (.conjR (.conjR hr))))) hz)) (.conjR hfD)
    exact eq_trans hy (eq_symm ho)
  | false =>
    have hfield := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B I t f A f n u i hw hL0 hc)) hfirst
    have hu := ForcingMemberGuard.identity_field hZ w A f I i u (.conjL (.conjR (.conjR (.conjR (.conjR hr))))) (.conjL hfield) (.conjR hfield)
    have hfD := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w V S t f z T n o i hw hLD hc)) hdirect
    exact ForcingMemberGuardOpening.free_image hZ w mode z a f T A C R S K H P r s i o u v y hf hu (.conjR hfD) hsecond hthird

private theorem term_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H P r s t B I V head n u v y o : Fin m)
    (hr : Derives Γ (input w mode z a f T A C R S K H P r s t B I V head)) (hp : Derives Γ (path w mode z a f T A C R S K H P r s t B I V head n u v y o)) : Derives Γ (.equal y o) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w B I t f A f n u (.conjL hp)
  apply Derives.disjE (.conjR ht)
  · let E := SyntaxTermSyntax.branch true w t n
    let D := SyntaxTermSyntax.branchWitness true w t n
    let Δ := Context.add D (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := D) (.hyp (Or.inl rfl))
    have hD : Derives Δ D := .hyp (Or.inl rfl)
    have hr1 := of_eq (input_rename w mode z a f T A C R S K H P r s t B I V head Fin.castSucc) (under (add hr E) D)
    have hp1 := of_eq (path_rename w mode z a f T A C R S K H P r s t B I V head n u v y o Fin.castSucc) (under (add hp E) D)
    exact variable_point (ZFContext.under (ZFContext.add hZ E) D) true
      w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc t.castSucc B.castSucc I.castSucc V.castSucc head.castSucc n.castSucc u.castSucc v.castSucc y.castSucc o.castSucc (Fin.last m) hr1 hp1 (.conjL hD) (.conjR hD)
  · let E := SyntaxTermSyntax.branch false w f n
    let D := SyntaxTermSyntax.branchWitness false w f n
    let Δ := Context.add D (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := D) (.hyp (Or.inl rfl))
    have hD : Derives Δ D := .hyp (Or.inl rfl)
    have hr1 := of_eq (input_rename w mode z a f T A C R S K H P r s t B I V head Fin.castSucc) (under (add hr E) D)
    have hp1 := of_eq (path_rename w mode z a f T A C R S K H P r s t B I V head n u v y o Fin.castSucc) (under (add hp E) D)
    exact variable_point (ZFContext.under (ZFContext.add hZ E) D) false
      w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc t.castSucc B.castSucc I.castSucc V.castSucc head.castSucc n.castSucc u.castSucc v.castSucc y.castSucc o.castSucc (Fin.last m) hr1 hp1 (.conjL hD) (.conjR hD)

def diagram {m} (w _mode z _a f T A C _R S K H _P r s t B I V _head : Fin m) : Formula m :=
  ForcingTermDiagram.diagram w (four t A C z) (four f f T T) (four B K r V) (four I H s S)
theorem diagram_rename {m l} (w mode z a f T A C R S K H P r s t B I V head : Fin m) (ρ : Fin m → Fin l) :
    (diagram w mode z a f T A C R S K H P r s t B I V head).rename ρ = diagram (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ t) (ρ B) (ρ I) (ρ V) (ρ head) := by
  simp only [diagram, ForcingTermDiagram.diagram_rename, four_map]

/-- All source and four output term candidates are quantified inside ZF.
The actual root one-slot table, identity free table, lifted opening and native
InstantiateTop environment suffice; no term/output equality oracle. -/
theorem root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z a f T A C R S K H P r s t B I V head : Fin m)
    (hr : Derives Γ (input w mode z a f T A C R S K H P r s t B I V head)) : Derives Γ (diagram w mode z a f T A C R S K H P r s t B I V head) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let D := path (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 t) (old 5 B) (old 5 I) (old 5 V) (old 5 head) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
  let Δ := Context.add D (raisedContext 5 Γ)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hr5 := of_eq (input_rename w mode z a f T A C R S K H P r s t B I V head (old 5)) (HornBinderRules.under_body 5 hr D)
  exact term_point (HornBinderRules.zf_body 5 hZ D) (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 t) (old 5 B) (old 5 I) (old 5 V) (old 5 head) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) hr5 hD

/-- Reuse the COMPLETED all-internal formula induction at these ACTUAL guard
tables. Works under every original binder, including nonstandard formula
codes; there is no new formula induction. -/
theorem cancel {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z a f T A C R S K H P r s t B I V head n q U Y O : Fin m)
    (hr : Derives Γ (input w mode z a f T A C R S K H P r s t B I V head))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B I t f A f n q))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q U))
    (h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U Y))
    (h3 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V S t f z T n O)) : Derives Γ (.equal Y O) := by
  exact ForcingFormulaInduction.cancel hZ w (four t A C z) (four f f T T) (four B K r V) (four I H s S)
    n q U Y O (.conjL (.conjL hr)) (root hZ w mode z a f T A C R S K H P r s t B I V head hr) h0 h1 h2 h3

def sentence {m} (w mode z a f T A C R S K H P r s t B I V head : Fin m) : Source.Sentence := ((input w mode z a f T A C R S K H P r s t B I V head).imp (diagram w mode z a f T A C R S K H P r s t B I V head)).close

theorem kernel_certificate {m} (w mode z a f T A C R S K H P r s t B I V head : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w mode z a f T A C R S K H P r s t B I V head)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact root (ZFContext.add (ZFContext.source_ZF m) (input w mode z a f T A C R S K H P r s t B I V head)) w mode z a f T A C R S K H P r s t B I V head (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingGuardDiagram
