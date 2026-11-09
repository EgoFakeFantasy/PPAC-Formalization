import PPAC.Migration.ForcingReflexiveImages
import PPAC.Migration.ForcingGuardOpening

/-! SAME original guard diagram, with only the selected p-slot in lifted H
replaced by target bound-zero. Full internal formula induction remains the
unchanged existing producer. No object truth or guard proof is assumed. -/
namespace PPAC.Migration.ForcingReflexiveDiagram
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

def input {m} (w mode z a f T A C R S K H P r s t B I V head j bzero EMap : Fin m) : Formula m :=
  (ForcingGuardDiagram.input w mode z a f T A C R S K H P r s t B I V head).conj
    ((ForcingReflexiveImages.replacement w f C T H j bzero EMap).conj
      ((SyntaxMixedImageHead.head w C T z bzero).conj (StructuralListFieldSyntax.field w S j P)))

theorem input_rename {m l} (w mode z a f T A C R S K H P r s t B I V head j bzero EMap : Fin m) (ρ : Fin m → Fin l) :
    (input w mode z a f T A C R S K H P r s t B I V head j bzero EMap).rename ρ = input (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ t) (ρ B) (ρ I) (ρ V) (ρ head) (ρ j) (ρ bzero) (ρ EMap) := by
  simp only [input, Formula.rename, ForcingGuardDiagram.input_rename, ForcingReflexiveImages.replacement_rename, SyntaxMixedImageHead.head_rename, StructuralListFieldSyntax.field_rename]

private def path {m} (w _mode z _a f T A C _R S K _H _P r s t B I V _head _j _bzero EMap n u v y o : Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w B I t f A f n u).conj
    ((SyntaxCodedMixedTermSyntax.substituted w K EMap A f C T u v).conj
      ((SyntaxCodedMixedTermSyntax.substituted w r s C T z T v y).conj
        (SyntaxCodedMixedTermSyntax.substituted w V S t f z T n o)))
private theorem path_rename {m l} (w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o : Fin m) (ρ : Fin m → Fin l) :
    (path w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o).rename ρ = path (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ t) (ρ B) (ρ I) (ρ V) (ρ head) (ρ j) (ρ bzero) (ρ EMap) (ρ n) (ρ u) (ρ v) (ρ y) (ρ o) := by
  simp only [path, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

private theorem variable_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool)
    (w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o i : Fin m)
    (hr : Derives Γ (input w mode z a f T A C R S K H P r s t B I V head j bzero EMap))
    (hp : Derives Γ (path w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o))
    (hi : Derives Γ (.mem i (SyntaxTermSyntax.limit bound t f)))
    (hc : Derives Γ (SyntaxVariableSyntax.code bound w i n)) : Derives Γ (.equal y o) := by
  have hb := Derives.conjL hr
  have hf := Derives.conjL hb
  have hw := Derives.conjL hf
  have hz := Derives.conjL (.conjR (.conjR hf))
  have hl := Derives.conjL (.conjR (.conjR (.conjR (.conjR hf))))
  have hKH := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H hl
  have hfirst := Derives.conjL hp
  have hsecond := Derives.conjL (.conjR hp)
  have hthird := Derives.conjL (.conjR (.conjR hp))
  have hdirect := Derives.conjR (.conjR (.conjR hp))
  have hL0 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w B I t f A f n u hfirst)
  have hLD := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w V S t f z T n o hdirect)
  cases bound with
  | true =>
    have hbelow := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ 1 t i (.conjL (.conjR hb)))) hi
    have hzi : Derives Γ (empty i) := .disjE hbelow (.botE (.hyp (Or.inl rfl))) (.hyp (Or.inl rfl))
    have heq := OmegaUniversal.empty_unique i z (ZFContext.arithmetic hZ).base.extensionality hzi hz
    have hcode := SyntaxVariableImagePoint.code_subst_index true w i n z heq hc
    have hfield := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w B I t f A f n u z hw hL0 hcode)) hfirst
    have hu := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ 1 w (fun _ => head) B 0 z u hw (.conjL (.conjR (.conjR (.conjR hb)))) hz)) (.conjR hfield)
    have hx := Derives.conjL (.conjR (.conjR hb))
    have hs' := SyntaxMixedFormulaAtomicSubst.term_source w K EMap A f C T u v head hu hsecond
    have hKD := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w K EMap A f C T head v hs')
    have hvK := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w K EMap A f C T head v z hw hKD hx)) hs'
    have hsH := Derives.impE (.conjR (SyntaxCodedMixedTermFields.at_field hZ true w K H A f C T head v z hw hKH hx)) hvK
    have hy := ForcingMemberGuardOpening.zero_image hZ w mode z a f T A C R S K H P r s head v y hf hx hsH hthird
    have hfD := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ true w V S t f z T n o z hw hLD hcode)) hdirect
    have ho := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ 1 w (fun _ => P) V 0 z o hw (.conjR (.conjR (.conjR (.conjR (.conjR hb))))) hz)) (.conjR hfD)
    exact eq_trans hy (eq_symm ho)
  | false =>
    have hfield := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w B I t f A f n u i hw hL0 hc)) hfirst
    have hu := ForcingMemberGuard.identity_field hZ w A f I i u (.conjL (.conjR (.conjR (.conjR (.conjR hb))))) (.conjL hfield) (.conjR hfield)
    have hfD := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w V S t f z T n o i hw hLD hc)) hdirect
    have hKD := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w K EMap A f C T u v hsecond)
    have hvD := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ false w K EMap A f C T u v i hw hKD hu)) hsecond
    have hRep := Derives.conjL (.conjR hr)
    have hCases := Derives.impE (.conjL (ForcingReflexiveImages.field_iff w f C T H j bzero EMap i v hRep (.conjL hvD))) (.conjR hvD)
    apply Derives.disjE hCases
    · let X := (Formula.equal i j).conj (.equal v bzero)
      let Δ := Context.add X Γ
      have hX : Derives Δ X := .hyp (Or.inl rfl)
      have hs0 := SyntaxMixedFormulaAtomicSubst.term_source w r s C T z T v y bzero (.conjR hX) (add hthird X)
      have hL1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted w r s C T z T bzero y hs0)
      have hHead := Derives.conjL (.conjR (.conjR hr))
      have hZeroCode := Derives.conjL (.conjR hHead)
      have ha := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field (ZFContext.add hZ X) true w r s C T z T bzero y z (add hw X) hL1 (add hZeroCode X))) hs0
      have henv := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))
      have hy := Derives.impE (.conjL (SyntaxTopCodedEnvironmentFields.instantiate_zero (ZFContext.add hZ X) w z T C P r s z y (add hw X) (add henv X) (add hz X))) ha
      have hSP := Derives.conjR (.conjR (.conjR hr))
      have hIP := StructuralListFieldSyntax.index_subst w S j i P (eq_symm (.conjL hX)) (add hSP X)
      have hiNat := StructuralListTraceOrder.member_member hZ w i f hw (.conjL (.conjR hKD)) (.conjL hvD)
      have ho := StructuralListFieldValues.unique (ZFContext.add hZ X) w S i o P (add hw X) (add hiNat X) (add (.conjR hfD) X) hIP
      exact eq_trans hy (eq_symm ho)
    · let X := ((Formula.equal i j).neg).conj (StructuralListFieldSyntax.field w H i v)
      have hX : Derives (Context.add X Γ) X := .hyp (Or.inl rfl)
      have hsH := Derives.impE (.conjR (SyntaxCodedMixedTermFields.at_field (ZFContext.add hZ X) false w K H A f C T u v i (add hw X) (add hKH X) (add hu X))) (.conjI (add (.conjL hvD) X) (.conjR hX))
      exact ForcingMemberGuardOpening.free_image (ZFContext.add hZ X) w mode z a f T A C R S K H P r s i o u v y (add hf X) (add hu X) (add (.conjR hfD) X) hsH (add hthird X)

private theorem term_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o : Fin m)
    (hr : Derives Γ (input w mode z a f T A C R S K H P r s t B I V head j bzero EMap)) (hp : Derives Γ (path w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o)) : Derives Γ (.equal y o) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w B I t f A f n u (.conjL hp)
  apply Derives.disjE (.conjR ht)
  · let E := SyntaxTermSyntax.branch true w t n
    let D := SyntaxTermSyntax.branchWitness true w t n
    let Δ := Context.add D (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := D) (.hyp (Or.inl rfl))
    have hD : Derives Δ D := .hyp (Or.inl rfl)
    have hr1 := of_eq (input_rename w mode z a f T A C R S K H P r s t B I V head j bzero EMap Fin.castSucc) (under (add hr E) D)
    have hp1 := of_eq (path_rename w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o Fin.castSucc) (under (add hp E) D)
    exact variable_point (ZFContext.under (ZFContext.add hZ E) D) true
      w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc t.castSucc B.castSucc I.castSucc V.castSucc head.castSucc j.castSucc bzero.castSucc EMap.castSucc n.castSucc u.castSucc v.castSucc y.castSucc o.castSucc (Fin.last m) hr1 hp1 (.conjL hD) (.conjR hD)
  · let E := SyntaxTermSyntax.branch false w f n
    let D := SyntaxTermSyntax.branchWitness false w f n
    let Δ := Context.add D (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := D) (.hyp (Or.inl rfl))
    have hD : Derives Δ D := .hyp (Or.inl rfl)
    have hr1 := of_eq (input_rename w mode z a f T A C R S K H P r s t B I V head j bzero EMap Fin.castSucc) (under (add hr E) D)
    have hp1 := of_eq (path_rename w mode z a f T A C R S K H P r s t B I V head j bzero EMap n u v y o Fin.castSucc) (under (add hp E) D)
    exact variable_point (ZFContext.under (ZFContext.add hZ E) D) false
      w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc t.castSucc B.castSucc I.castSucc V.castSucc head.castSucc j.castSucc bzero.castSucc EMap.castSucc n.castSucc u.castSucc v.castSucc y.castSucc o.castSucc (Fin.last m) hr1 hp1 (.conjL hD) (.conjR hD)

def diagram {m} (w mode z a f T A C R S K _H P r s t B I V head _j _bzero EMap : Fin m) : Formula m :=
  ForcingGuardDiagram.diagram w mode z a f T A C R S K EMap P r s t B I V head

theorem diagram_rename {m l} (w mode z a f T A C R S K H P r s t B I V head j bzero EMap : Fin m) (ρ : Fin m → Fin l) :
    (diagram w mode z a f T A C R S K H P r s t B I V head j bzero EMap).rename ρ = diagram (ρ w) (ρ mode) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ t) (ρ B) (ρ I) (ρ V) (ρ head) (ρ j) (ρ bzero) (ρ EMap) := by
  simp only [diagram, ForcingGuardDiagram.diagram_rename]

theorem root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z a f T A C R S K H P r s t B I V head j bzero EMap : Fin m)
    (hr : Derives Γ (input w mode z a f T A C R S K H P r s t B I V head j bzero EMap)) : Derives Γ (diagram w mode z a f T A C R S K H P r s t B I V head j bzero EMap) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let D := path (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 t) (old 5 B) (old 5 I) (old 5 V) (old 5 head) (old 5 j) (old 5 bzero) (old 5 EMap) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)
  let Δ := Context.add D (raisedContext 5 Γ)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hr5 := of_eq (input_rename w mode z a f T A C R S K H P r s t B I V head j bzero EMap (old 5)) (HornBinderRules.under_body 5 hr D)
  exact term_point (HornBinderRules.zf_body 5 hZ D) (old 5 w) (old 5 mode) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 t) (old 5 B) (old 5 I) (old 5 V) (old 5 head) (old 5 j) (old 5 bzero) (old 5 EMap) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) hr5 hD

private theorem at_direct {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s head j Q bzero EMap F X Y : Fin m) (v : Fin 4 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hm : Derives Γ (ForcingGuardCode.matrix order Reln w A f head Q v))
    (hd : Derives Γ (ForcingReflexiveImages.diagonalData w z f T A C K H j Q bzero EMap F))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F X))
    (hj : Derives Γ (StructuralListFieldSyntax.field w S j P))
    (ho : Derives Γ (ForcingGuardOpening.direct w z f T P S (v 0) (v 1) Y)) : Derives Γ (.equal X Y) := by
  let V := (SyntaxForestSyntax.forest 1 w.castSucc (fun _ => P.castSucc) (Fin.last m)).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (Fin.last m) S.castSucc (v 0).castSucc f.castSucc z.castSucc T.castSucc (v 1).castSucc Y.castSucc)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) ho
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ V
  have hf1 := of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C R S K H P r s Fin.castSucc) (under hf V)
  have hx1 := of_eq (SyntaxVariableSyntax.code_rename true w z head Fin.castSucc) (under hx V)
  have hm1 := of_eq (ForcingGuardCode.matrix_rename order Reln w A f head Q v Fin.castSucc) (under hm V)
  have hd1 := of_eq (ForcingReflexiveImages.diagonalData_rename w z f T A C K H j Q bzero EMap F Fin.castSucc) (under hd V)
  have hi1 := of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C P F X Fin.castSucc) (under hi V)
  have hj1 := of_eq (StructuralListFieldSyntax.field_rename w S j P Fin.castSucc) (under hj V)
  have hb : Derives Δ (ForcingGuardDiagram.input w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc (v 0).castSucc (v 2).castSucc (v 3).castSucc (Fin.last m) head.castSucc) :=
    .conjI hf1 (.conjI (.conjL hm1) (.conjI hx1 (.conjI (.conjL (.conjR (.conjR hm1))) (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hm1))))) (.conjL hV)))))
  have hr : Derives Δ (input w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc (v 0).castSucc (v 2).castSucc (v 3).castSucc (Fin.last m) head.castSucc j.castSucc bzero.castSucc EMap.castSucc) :=
    .conjI hb (.conjI (.conjL (.conjR hd1)) (.conjI (.conjL hd1) hj1))
  have hRoot := root hZ1 w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc (v 0).castSucc (v 2).castSucc (v 3).castSucc (Fin.last m) head.castSucc j.castSucc bzero.castSucc EMap.castSucc hr
  have henv := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hf1)))))
  have hinst := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ1 w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc F.castSucc X.castSucc r.castSucc s.castSucc (.conjL hf1) henv)) hi1
  exact ForcingFormulaInduction.cancel hZ1 w.castSucc
    (four (v 0).castSucc A.castSucc C.castSucc z.castSucc) (four f.castSucc f.castSucc T.castSucc T.castSucc)
    (four (v 2).castSucc K.castSucc r.castSucc (Fin.last m)) (four (v 3).castSucc EMap.castSucc s.castSucc S.castSucc)
    (v 1).castSucc Q.castSucc F.castSucc X.castSucc Y.castSucc (.conjL hf1) hRoot
    (.conjR (.conjR (.conjR (.conjR (.conjR hm1))))) (.conjR (.conjR hd1)) hinst (.conjR hV)

/-- SAME actual original guard instance and actual diagonal body instance
have identical output. Selected p-field equality is consumed, never assumed
as an output equality. All compiler/direct-table witnesses are eliminated. -/
theorem commutes {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s own head j Q U Y bzero EMap F X : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f head Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P U Y))
    (hd : Derives Γ (ForcingReflexiveImages.diagonalData w z f T A C K H j Q bzero EMap F))
    (hX : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F X))
    (hj : Derives Γ (StructuralListFieldSyntax.field w S j P)) : Derives Γ (.equal X Y) := by
  have hActual := ForcingGuardOpening.from_instance hZ order Reln w mode z a f T A C R S K H P r s own head Q U Y hf hh hc ho hi
  have heq := OmegaUniversal.empty_unique own z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) (.conjL (.conjR (.conjR hf)))
  have hx := SyntaxVariableImagePoint.code_subst_index true w own head z heq (.conjL (.conjR hh))
  let B := ForcingGuardOpening.body order Reln w z f T P S A head Q Y
  let Δ := Context.add B (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 B _ hActual
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact at_direct (HornBinderRules.zf_body 4 hZ B) order Reln
    (old 4 w) (old 4 mode) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (old 4 P) (old 4 r) (old 4 s) (old 4 head) (old 4 j) (old 4 Q) (old 4 bzero) (old 4 EMap) (old 4 F) (old 4 X) (old 4 Y) (slot 4)
    (of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C R S K H P r s (old 4)) (HornBinderRules.under_body 4 hf B))
    (of_eq (SyntaxVariableSyntax.code_rename true w z head (old 4)) (HornBinderRules.under_body 4 hx B)) (.conjL hB)
    (of_eq (ForcingReflexiveImages.diagonalData_rename w z f T A C K H j Q bzero EMap F (old 4)) (HornBinderRules.under_body 4 hd B))
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C P F X (old 4)) (HornBinderRules.under_body 4 hX B))
    (of_eq (StructuralListFieldSyntax.field_rename w S j P (old 4)) (HornBinderRules.under_body 4 hj B)) (.conjR hB)

private theorem instance_target_subst {m} {Γ : Context m} (w z T C P F X Y : Fin m)
    (he : Derives Γ (.equal X Y)) (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F X)) :
    Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F Y) := by
  let B := SyntaxTopFormulaSyntax.instantiated w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc F.castSucc (Fin.last m)
  have hx : B.instantiate X = SyntaxTopFormulaSyntax.instantiated w z T C P F X := by
    simp only [B, Formula.instantiate, SyntaxTopFormulaSyntax.instantiated_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hy : B.instantiate Y = SyntaxTopFormulaSyntax.instantiated w z T C P F Y := by
    simp only [B, Formula.instantiate, SyntaxTopFormulaSyntax.instantiated_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hy (Derives.eqSubst B he (of_eq hx.symm hi))

def resultData {m} (w z f T A C K H P j Q Y bzero EMap F : Fin m) : Formula m :=
  (ForcingReflexiveImages.diagonalData w z f T A C K H j Q bzero EMap F).conj
    (SyntaxTopFormulaSyntax.instantiated w z T C P F Y)

theorem resultData_rename {m l} (w z f T A C K H P j Q Y bzero EMap F : Fin m) (ρ : Fin m → Fin l) :
    (resultData w z f T A C K H P j Q Y bzero EMap F).rename ρ = resultData (ρ w) (ρ z) (ρ f) (ρ T) (ρ A) (ρ C) (ρ K) (ρ H) (ρ P) (ρ j) (ρ Q) (ρ Y) (ρ bzero) (ρ EMap) (ρ F) := by
  simp only [resultData, Formula.rename, ForcingReflexiveImages.diagonalData_rename, SyntaxTopFormulaSyntax.instantiated_rename]

def resultBody {m} (w z f T A C K H P j Q Y : Fin m) : Formula (m+3) :=
  resultData (old 3 w) (old 3 z) (old 3 f) (old 3 T) (old 3 A) (old 3 C) (old 3 K) (old 3 H) (old 3 P) (old 3 j) (old 3 Q) (old 3 Y) (slot 3 0) (slot 3 1) (slot 3 2)

def result {m} (w z f T A C K H P j Q Y : Fin m) : Formula m := existsMany 3 (resultBody w z f T A C K H P j Q Y)

theorem result_rename {m l} (w z f T A C K H P j Q Y : Fin m) (ρ : Fin m → Fin l) :
    (result w z f T A C K H P j Q Y).rename ρ = result (ρ w) (ρ z) (ρ f) (ρ T) (ρ A) (ρ C) (ρ K) (ρ H) (ρ P) (ρ j) (ρ Q) (ρ Y) := by
  simp only [result, existsMany_rename, resultBody, resultData_rename, lift_old, lift_slot]

/-- For ANY actual chosen diagonal body, generate its native instance and
identify it with the SAME original guard output. This lets both guards share
one replacement table; no instance/equality output is supplied. -/
theorem at_body {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s own head j Q U Y bzero EMap F : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f head Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P U Y))
    (hd : Derives Γ (ForcingReflexiveImages.diagonalData w z f T A C K H j Q bzero EMap F))
    (hj : Derives Γ (StructuralListFieldSyntax.field w S j P)) :
    Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P F Y) := by
  have hP := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hf)))))
  have hl := Derives.conjL (.conjR (.conjR (.conjR (.conjR hf))))
  have hC := Derives.conjR (.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T A C K H hl))
  have hF := SyntaxMixedFormulaJudgment.target_type w K EMap A f C T Q F (.conjR (.conjR hd))
  have he := SyntaxTopFormulaExistence.instantiate_exists hZ w z T C P F (.conjL hf) (.conjI (.conjI hP hC) hF)
  let X := SyntaxTopFormulaSyntax.instantiated w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc F.castSucc (Fin.last m)
  let Δ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) he
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have lift1 {B : Formula m} (hB : Derives Γ B) := under hB X
  have hEq := commutes (ZFContext.under hZ X) order Reln
    w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc own.castSucc head.castSucc j.castSucc Q.castSucc U.castSucc Y.castSucc bzero.castSucc EMap.castSucc F.castSucc (Fin.last m)
    (of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C R S K H P r s Fin.castSucc) (lift1 hf))
    (of_eq (SyntaxMixedImageHead.head_rename w A f own head Fin.castSucc) (lift1 hh))
    (of_eq (ForcingGuardCode.compiled_rename order Reln w A f head Q Fin.castSucc) (lift1 hc))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T Q U Fin.castSucc) (lift1 ho))
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C P U Y Fin.castSucc) (lift1 hi))
    (of_eq (ForcingReflexiveImages.diagonalData_rename w z f T A C K H j Q bzero EMap F Fin.castSucc) (lift1 hd)) hX
    (of_eq (StructuralListFieldSyntax.field_rename w S j P Fin.castSucc) (lift1 hj))
  exact of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C P F Y Fin.castSucc).symm
    (instance_target_subst w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc F.castSucc (Fin.last m) Y.castSucc hEq hX)

/-- Internally BUILD the target head, updated table, body and native instance.
The SAME original guard output Y is the actual instance of that body at P.
No output, environment, term-diagram or equality witness is supplied. -/
theorem from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s own head j Q U Y : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f own head))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f head Q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T Q U))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P U Y))
    (_hn : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j))
    (hj : Derives Γ (StructuralListFieldSyntax.field w S j P)) :
    Derives Γ (result w z f T A C K H P j Q Y) := by
  have he := ForcingReflexiveImages.from_compiled hZ order Reln w mode z a f T A C R S K H P r s j head Q hf hc
  let B := ForcingReflexiveImages.diagonalBody w z f T A C K H j Q
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 B _ he
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have lift3 {X : Formula m} (hX : Derives Γ X) := HornBinderRules.under_body 3 hX B
  have hSame := at_body (HornBinderRules.zf_body 3 hZ B) order Reln
    (old 3 w) (old 3 mode) (old 3 z) (old 3 a) (old 3 f) (old 3 T) (old 3 A) (old 3 C) (old 3 R) (old 3 S) (old 3 K) (old 3 H) (old 3 P) (old 3 r) (old 3 s) (old 3 own) (old 3 head) (old 3 j) (old 3 Q) (old 3 U) (old 3 Y) (slot 3 0) (slot 3 1) (slot 3 2)
    (of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C R S K H P r s (old 3)) (lift3 hf))
    (of_eq (SyntaxMixedImageHead.head_rename w A f own head (old 3)) (lift3 hh))
    (of_eq (ForcingGuardCode.compiled_rename order Reln w A f head Q (old 3)) (lift3 hc))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T Q U (old 3)) (lift3 ho))
    (of_eq (SyntaxTopFormulaSyntax.instantiated_rename w z T C P U Y (old 3)) (lift3 hi)) hB
    (of_eq (StructuralListFieldSyntax.field_rename w S j P (old 3)) (lift3 hj))
  have hout : Derives Δ (result (old 3 w) (old 3 z) (old 3 f) (old 3 T) (old 3 A) (old 3 C) (old 3 K) (old 3 H) (old 3 P) (old 3 j) (old 3 Q) (old 3 Y)) := by
    apply HornBinderRules.intro_many 3 _ (slot 3)
    exact of_eq (by simp only [resultBody, resultData_rename, assign_old, assign_slot]; rfl) (.conjI hB hSame)
  exact of_eq (result_rename w z f T A C K H P j Q Y (old 3)).symm hout

def sourceInput {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s own head j Q U Y : Fin m) : Formula m :=
  (ForcingGuardOpening.input order Reln w mode z a f T A C R S K H P r s own head Q U Y).conj
    ((SyntaxNumeralSyntax.numeral (k+1) j).conj (StructuralListFieldSyntax.field w S j P))

def sentence {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s own head j Q U Y : Fin m) : Source.Sentence :=
  ((sourceInput order Reln w mode z a f T A C R S K H P r s own head j Q U Y).imp (result w z f T A C K H P j Q Y)).close

theorem kernel_certificate {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s own head j Q U Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence order Reln w mode z a f T A C R S K H P r s own head j Q U Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := sourceInput order Reln w mode z a f T A C R S K H P r s own head j Q U Y
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  have hs := Derives.conjL h
  exact from_instance (ZFContext.add (ZFContext.source_ZF m) E) order Reln w mode z a f T A C R S K H P r s own head j Q U Y
    (.conjL hs) (.conjL (.conjR hs)) (.conjL (.conjR (.conjR hs))) (.conjL (.conjR (.conjR (.conjR hs)))) (.conjR (.conjR (.conjR (.conjR hs)))) (.conjL (.conjR h)) (.conjR (.conjR h))

end PPAC.Migration.ForcingReflexiveDiagram
