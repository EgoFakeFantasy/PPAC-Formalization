import PPAC.Migration.ForcingGuardDiagram
import PPAC.Migration.ForcingRelationGuardFormula

/-! Actual original member OR relation guard compilation, lifted opening and
native InstantiateTop output is a DIRECT substitution of the SAME original
guard quotation by bound table [P] and SAME original free table S. This is
syntactic commutation, not an internal proof of either guard or forcing MP. -/
namespace PPAC.Migration.ForcingGuardOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def direct {m} (w z f T P S t N Y : Fin m) : Formula m := .ex
  ((SyntaxForestSyntax.forest 1 w.castSucc (fun _ => P.castSucc) (Fin.last m)).conj
    (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (Fin.last m) S.castSucc t.castSucc f.castSucc z.castSucc T.castSucc N.castSucc Y.castSucc))
theorem direct_rename {m l} (w z f T P S t N Y : Fin m) (ρ : Fin m → Fin l) :
    (direct w z f T P S t N Y).rename ρ = direct (ρ w) (ρ z) (ρ f) (ρ T) (ρ P) (ρ S) (ρ t) (ρ N) (ρ Y) := by
  simp only [direct, Formula.rename, SyntaxForestSyntax.forest_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem at_bound_map {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s head q U Y V : Fin m) (v : Fin 4 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hm : Derives Γ (ForcingGuardCode.matrix order Reln w A f head q v))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q U))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V S (v 0) f z T (v 1) Y) := by
  have hw := Derives.conjL hf
  have hp := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have he := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have hFirst := Derives.conjR (.conjR (.conjR (.conjR (.conjR hm))))
  have hRoot : Derives Γ (ForcingGuardDiagram.input w mode z a f T A C R S K H P r s (v 0) (v 2) (v 3) V head) :=
    .conjI hf (.conjI (.conjL hm) (.conjI hh (.conjI (.conjL (.conjR (.conjR hm)))
      (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hm))))) hV))))
  have hVtype := ForcingAtomicCode.bound_forest_typed hZ w (v 0) z T V (fun _ => P) hw (.conjL hm) (.conjL hp) (fun _ => hp) hV
  have hStype := Derives.conjR (ForcingOpenLayout.environment_types w z a f T R S he)
  have hNtype := Derives.conjR (.conjL (.conjR hm))
  have hDirect := SyntaxMixedFormulaOutputInduction.actual_exists hZ w V S (v 0) f z T (v 1) hw (.conjI hNtype (.conjI hVtype hStype))
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc V.castSucc S.castSucc (v 0).castSucc f.castSucc z.castSucc T.castSucc (v 1).castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hDirect
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hRoot1 := of_eq (ForcingGuardDiagram.input_rename w mode z a f T A C R S K H P r s (v 0) (v 2) (v 3) V head Fin.castSucc) (under hRoot E)
  have hFirst1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w (v 2) (v 3) (v 0) f A f (v 1) q Fin.castSucc) (under hFirst E)
  have ho1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T q U Fin.castSucc) (under ho E)
  have hi1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T U Y Fin.castSucc) (under hi E)
  have heq := ForcingGuardDiagram.cancel (ZFContext.under hZ E) w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc
    (v 0).castSucc (v 2).castSucc (v 3).castSucc V.castSucc head.castSucc (v 1).castSucc q.castSucc U.castSucc Y.castSucc (Fin.last m)
    hRoot1 hFirst1 ho1 hi1 hE
  have hout := SyntaxMixedFormulaJudgmentSubst.subst_q w.castSucc V.castSucc S.castSucc (v 0).castSucc f.castSucc z.castSucc T.castSucc
    (v 1).castSucc (Fin.last m) Y.castSucc (eq_symm heq) hE
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V S (v 0) f z T (v 1) Y Fin.castSucc).symm hout

theorem from_matrix {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s head q U Y : Fin m) (v : Fin 4 → Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hm : Derives Γ (ForcingGuardCode.matrix order Reln w A f head q v))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q U))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U Y)) :
    Derives Γ (direct w z f T P S (v 0) (v 1) Y) := by
  have hp := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have hw := Derives.conjL hf
  have hNat := SyntaxTerms.range hZ w z T P hw hp
  have hForest := SyntaxForests.exists_forest hZ 1 w (fun _ => P) hw (.conjI hNat (.eqRefl w))
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxForestSyntax.forest 1 w.castSucc (fun _ => P.castSucc) (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hForest
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hf1 := of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C R S K H P r s Fin.castSucc) (under hf E)
  have hh1 := of_eq (SyntaxVariableSyntax.code_rename true w z head Fin.castSucc) (under hh E)
  have hm1 := of_eq (ForcingGuardCode.matrix_rename order Reln w A f head q v Fin.castSucc) (under hm E)
  have ho1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T q U Fin.castSucc) (under ho E)
  have hi1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T U Y Fin.castSucc) (under hi E)
  have hd := at_bound_map (ZFContext.under hZ E) order Reln w.castSucc mode.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc
    head.castSucc q.castSucc U.castSucc Y.castSucc (Fin.last m) (fun i => (v i).castSucc) hf1 hh1 hm1 (.conjR hE) ho1 hi1
  have hout : Derives Δ (direct w.castSucc z.castSucc f.castSucc T.castSucc P.castSucc S.castSucc (v 0).castSucc (v 1).castSucc Y.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxForestSyntax.forest_rename,
      SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjR hE) hd)
  exact of_eq (direct_rename w z f T P S (v 0) (v 1) Y Fin.castSucc).symm hout

def data {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w z f T P S A head q Y : Fin m) (v : Fin 4 → Fin m) : Formula m :=
  (ForcingGuardCode.matrix order Reln w A f head q v).conj (direct w z f T P S (v 0) (v 1) Y)
theorem data_rename {k m l} (order : Bool) (Reln : Source.Formula (k+2)) (w z f T P S A head q Y : Fin m) (v : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (data order Reln w z f T P S A head q Y v).rename ρ = data order Reln (ρ w) (ρ z) (ρ f) (ρ T) (ρ P) (ρ S) (ρ A) (ρ head) (ρ q) (ρ Y) (fun i => ρ (v i)) := by
  simp only [data, Formula.rename, ForcingGuardCode.matrix_rename, direct_rename]
def body {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w z f T P S A head q Y : Fin m) : Formula (m+4) :=
  data order Reln (old 4 w) (old 4 z) (old 4 f) (old 4 T) (old 4 P) (old 4 S) (old 4 A) (old 4 head) (old 4 q) (old 4 Y) (slot 4)
def result {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w z f T P S A head q Y : Fin m) : Formula m :=
  existsMany 4 (body order Reln w z f T P S A head q Y)
theorem result_rename {k m l} (order : Bool) (Reln : Source.Formula (k+2)) (w z f T P S A head q Y : Fin m) (ρ : Fin m → Fin l) :
    (result order Reln w z f T P S A head q Y).rename ρ = result order Reln (ρ w) (ρ z) (ρ f) (ρ T) (ρ P) (ρ S) (ρ A) (ρ head) (ρ q) (ρ Y) := by
  simp only [result, existsMany_rename, body, data_rename, lift_old, lift_slot]

/-- Consume the actual compiler directly; the SAME four compiler witnesses
are internally eliminated, and the same actual output Y satisfies the direct
substitution judgment. The guard quotation/free table are preserved exactly. -/
theorem from_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s head q U Y : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f head q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q U))
    (hi : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T U Y)) :
    Derives Γ (result order Reln w z f T P S A head q Y) := by
  let E := ForcingGuardCode.body order Reln w A f head q
  let Δ := Context.add E (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 E _ hc
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hf4 := of_eq (ForcingMemberGuardOpening.frame_rename w mode z a f T A C R S K H P r s (old 4)) (HornBinderRules.under_body 4 hf E)
  have hh4 := of_eq (SyntaxVariableSyntax.code_rename true w z head (old 4)) (HornBinderRules.under_body 4 hh E)
  have ho4 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T q U (old 4)) (HornBinderRules.under_body 4 ho E)
  have hi4 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w r s C T z T U Y (old 4)) (HornBinderRules.under_body 4 hi E)
  have hd := from_matrix (HornBinderRules.zf_body 4 hZ E) order Reln (old 4 w) (old 4 mode) (old 4 z) (old 4 a) (old 4 f) (old 4 T) (old 4 A) (old 4 C) (old 4 R) (old 4 S) (old 4 K) (old 4 H) (old 4 P) (old 4 r) (old 4 s)
    (old 4 head) (old 4 q) (old 4 U) (old 4 Y) (slot 4) hf4 hh4 hE ho4 hi4
  have hout : Derives Δ (result order Reln (old 4 w) (old 4 z) (old 4 f) (old 4 T) (old 4 P) (old 4 S) (old 4 A) (old 4 head) (old 4 q) (old 4 Y)) := by
    apply HornBinderRules.intro_many 4 _ (slot 4)
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) (.conjI hE hd)
  exact of_eq (result_rename order Reln w z f T P S A head q Y (old 4)).symm hout

/-- A compiler's one bound image is the actual head, and its free images
preserve their literal indices. Compare the subsequent mixed lift with the
single direct query on precisely those target fields. -/
private theorem lifted_guard_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f c d t B F K H V head P x u q y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral 1 t))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hB : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => head) B))
    (hF : Derives Γ (ForcingAtomicCode.identityImages w a f F))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Derives Γ (StructuralListFieldSyntax.field w K z P))
    (hPath : Derives Γ (ForcingRelationImages.guardPath w t f a c d B F K H V H x u q y)) :
    Derives Γ (.equal q y) := by
  let out := Formula.equal q y
  have hx := SyntaxCodedMixedTermTyping.source_type w B F t f a f x u (.conjL hPath)
  apply Derives.disjE (.conjR hx)
  · let E := SyntaxTermSyntax.branch true w t x
    let Q := SyntaxTermSyntax.branchWitness true w t x
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w t x out (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    let r := Fin.castSucc (n := m)
    let i := Fin.last m
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ (P.rename r) := under (add h E) Q
    have hZ1 := ZFContext.under (ZFContext.add hZ E) Q
    have hw1 := of_eq (omega_rename w r) (lift hw)
    have hz1 := of_eq (empty_rename z r) (lift hz)
    have ht1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 t r) (lift ht)
    have hi := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ1 1 (r t) i ht1)) (.conjL hQ)
    have hi0 : Derives Δ (empty i) :=
      .disjE hi (.botE (.hyp (Or.inl rfl))) (.hyp (Or.inl rfl))
    have ei := OmegaUniversal.empty_unique i (r z) (ZFContext.arithmetic hZ1).base.extensionality hi0 hz1
    have hx1 := SyntaxVariableImagePoint.code_subst_index true (r w) i (r x) (r z) ei (.conjR hQ)
    have path := of_eq (ForcingRelationImages.guardPath_rename w t f a c d B F K H V H x u q y r) (lift hPath)
    have p0 := Derives.conjL path
    have p1 := Derives.conjL (.conjR path)
    have p2 := Derives.conjR (.conjR path)
    have L0 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted (r w) (r B) (r F) (r t) (r f) (r a) (r f) (r x) (r u) p0)
    have L1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted (r w) (r K) (r H) (r a) (r f) (r c) (r d) (r u) (r q) p1)
    have L2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted (r w) (r V) (r H) (r t) (r f) (r c) (r d) (r x) (r y) p2)
    have f0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 true (r w) (r B) (r F) (r t) (r f) (r a) (r f) (r x) (r u) (r z) hw1 L0 hx1)) p0
    have f2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 true (r w) (r V) (r H) (r t) (r f) (r c) (r d) (r x) (r y) (r z) hw1 L2 hx1)) p2
    have e0 := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ1 1 (r w) (fun _ => r head) (r B) 0 (r z) (r u)
      hw1 (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => head) B r) (lift hB)) hz1)) (.conjR f0)
    have e2 := Derives.impE (.conjL (SyntaxForestFieldValues.field_at hZ1 1 (r w) (fun _ => r P) (r V) 0 (r z) (r y)
      hw1 (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => P) V r) (lift hV)) hz1)) (.conjR f2)
    have p1' := SyntaxMixedFormulaAtomicSubst.term_source (r w) (r K) (r H) (r a) (r f) (r c) (r d) (r u) (r q) (r head) e0 p1
    have f1 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 true (r w) (r K) (r H) (r a) (r f) (r c) (r d) (r head) (r q) (r z) hw1 L1
      (of_eq (SyntaxVariableSyntax.code_rename true w z head r) (lift hh)))) p1'
    have hzW := OmegaStructureAlgebra.zero_member (r w) (r z) (ZFContext.arithmetic hZ1).base.extensionality hw1 hz1
    have e1 := StructuralListFieldValues.unique hZ1 (r w) (r K) (r z) (r q) (r P) hw1 hzW
      (.conjR f1) (of_eq (StructuralListFieldSyntax.field_rename w K z P r) (lift hK))
    exact eq_trans e1 (eq_symm e2)
  · let E := SyntaxTermSyntax.branch false w f x
    let Q := SyntaxTermSyntax.branchWitness false w f x
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w f x out (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    let r := Fin.castSucc (n := m)
    let i := Fin.last m
    have lift {P : Formula m} (h : Derives Γ P) : Derives Δ (P.rename r) := under (add h E) Q
    have hZ1 := ZFContext.under (ZFContext.add hZ E) Q
    have hw1 := of_eq (omega_rename w r) (lift hw)
    have path := of_eq (ForcingRelationImages.guardPath_rename w t f a c d B F K H V H x u q y r) (lift hPath)
    have p0 := Derives.conjL path
    have p1 := Derives.conjL (.conjR path)
    have p2 := Derives.conjR (.conjR path)
    have L0 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted (r w) (r B) (r F) (r t) (r f) (r a) (r f) (r x) (r u) p0)
    have L1 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted (r w) (r K) (r H) (r a) (r f) (r c) (r d) (r u) (r q) p1)
    have L2 := Derives.conjL (SyntaxCodedMixedTermTyping.input_of_substituted (r w) (r V) (r H) (r t) (r f) (r c) (r d) (r x) (r y) p2)
    have f0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false (r w) (r B) (r F) (r t) (r f) (r a) (r f) (r x) (r u) i hw1 L0 (.conjR hQ))) p0
    have hu := ForcingMemberGuard.identity_field hZ1 (r w) (r a) (r f) (r F) i (r u)
      (of_eq (ForcingAtomicCode.identityImages_rename w a f F r) (lift hF)) (.conjL f0) (.conjR f0)
    have f1 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false (r w) (r K) (r H) (r a) (r f) (r c) (r d) (r u) (r q) i hw1 L1 hu)) p1
    have f2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false (r w) (r V) (r H) (r t) (r f) (r c) (r d) (r x) (r y) i hw1 L2 (.conjR hQ))) p2
    have hfW := Derives.conjR (.conjL (SyntaxCodedMixedTermTyping.source_type (r w) (r B) (r F) (r t) (r f) (r a) (r f) (r x) (r u) p0))
    have hiW := StructuralListTraceOrder.member_member hZ1 (r w) i (r f) hw1 hfW (.conjL f0)
    exact StructuralListFieldValues.unique hZ1 (r w) (r H) i (r q) (r y) hw1 hiW (.conjR f1) (.conjR f2)

private theorem lifted_guard_query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (k+2))
    (w z a f c d K H head P q Y V : Fin m) (v : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (hp : Derives Γ (SyntaxTermSyntax.term w c d P))
    (hK : Derives Γ (StructuralListFieldSyntax.field w K z P))
    (hm : Derives Γ (ForcingGuardCode.matrix order R w a f head q v))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hY : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H a f c d q Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V H (v 0) f c d (v 1) Y) := by
  have ht := Derives.conjL hm
  have hB := Derives.conjL (.conjR (.conjR hm))
  have hF := Derives.conjL (.conjR (.conjR (.conjR (.conjR hm))))
  have h0 := Derives.conjR (.conjR (.conjR (.conjR (.conjR hm))))
  have hS := Derives.conjL (.conjR (FormulaCodeProperties.guards w (v 1) (v 0) f (.conjR (.conjL (.conjR hm)))))
  have hf := Derives.conjR (.conjR (FormulaCodeProperties.guards w (v 1) (v 0) f (.conjR (.conjL (.conjR hm)))))
  have hH := Derives.conjR (.conjR (SyntaxMixedFormulaOutput.input_of_substituted hZ w K H a f c d q Y hw hY))
  have hTyped := ForcingAtomicCode.bound_forest_typed hZ w (v 0) c d V (fun _ => P) hw ht (.conjL hp) (fun _ => hp) hV
  apply ForcingRelationGuardFormula.to_direct_at_scope hZ w (v 0) f a c d (v 2) (v 3) K H V H (v 1) q Y hw hS hf hTyped hH h0 hY
  intro l Δ r hZ1 lift x u q y hPath
  exact lifted_guard_term hZ1 (r w) (r z) (r a) (r f) (r c) (r d) (r (v 0)) (r (v 2)) (r (v 3))
    (r K) (r H) (r V) (r head) (r P) x u q y (of_eq (omega_rename w r) (lift hw)) (of_eq (empty_rename z r) (lift hz))
    (of_eq (SyntaxNumeralSyntax.numeral_rename 1 (v 0) r) (lift ht))
    (of_eq (SyntaxVariableSyntax.code_rename true w z head r) (lift hh))
    (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => head) (v 2) r) (lift hB))
    (of_eq (ForcingAtomicCode.identityImages_rename w a f (v 3) r) (lift hF))
    (of_eq (SyntaxForestSyntax.forest_rename 1 w (fun _ => P) V r) (lift hV))
    (of_eq (StructuralListFieldSyntax.field_rename w K z P r) (lift hK)) hPath

/-- Read an actual guard compiler and its lifted query. The same
output is the native guard quotation queried with the original free table
and the actual image of the compiler's bound head. Target scopes remain internal. -/
theorem from_lifted_at {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (k+2))
    (w z a f c d K H head P q Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (ha : Derives Γ (.mem z a))
    (hK : Derives Γ (StructuralListFieldSyntax.field w K z P))
    (hq : Derives Γ (ForcingGuardCode.compiled order R w a f head q))
    (hY : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H a f c d q Y)) :
    Derives Γ (result order R w c f d P H a head q Y) := by
  have hi := SyntaxMixedFormulaOutput.input_of_substituted hZ w K H a f c d q Y hw hY
  have hp := SyntaxMixedImageCodeFields.field_type w a c d K z P (.conjL (.conjR hi)) ha hK
  let out := result order R w c f d P H a head q Y
  let M := ForcingGuardCode.body order R w a f head q
  let Δ := Context.add M (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 M out hq
  have hM : Derives Δ M := .hyp (Or.inl rfl)
  let r := old (m := m) 4
  let v := slot (m := m) 4
  have lift {P : Formula m} (h : Derives Γ P) : Derives Δ (P.rename r) := HornBinderRules.under_body 4 h M
  have hZ1 := HornBinderRules.zf_body 4 hZ M
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hN := SyntaxTerms.range hZ1 (r w) (r c) (r d) (r P) hw1 (of_eq (SyntaxTermSyntax.term_rename w c d P r) (lift hp))
  have existsV := SyntaxForests.exists_forest hZ1 1 (r w) (fun _ => r P) hw1 (.conjI hN (.eqRefl (r w)))
  let liftedResult := result order R (r w) (r c) (r f) (r d) (r P) (r H) (r a) (r head) (r q) (r Y)
  have hResult : Derives Δ liftedResult := by
    let E := (Formula.mem (Fin.last (m+4)) (r w).castSucc).conj
      (SyntaxForestSyntax.forest 1 (r w).castSucc (fun _ => (r P).castSucc) (Fin.last (m+4)))
    let Ξ := Context.add E (Context.image Formula.raise Δ)
    apply Derives.exE (p := E) existsV
    let s := Fin.castSucc ∘ r
    let V := Fin.last (m+4)
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have carry {P : Formula m} (h : Derives Γ P) : Derives Ξ (P.rename s) :=
      of_eq (SourceAlgebra.rename_comp P r Fin.castSucc) (under (lift h) E)
    have hM1 := of_eq (ForcingGuardCode.matrix_rename order R (r w) (r a) (r f) (r head) (r q) v Fin.castSucc) (under hM E)
    have h := lifted_guard_query (ZFContext.under hZ1 E) order R (s w) (s z) (s a) (s f) (s c) (s d)
      (s K) (s H) (s head) (s P) (s q) (s Y) V (fun i => (v i).castSucc)
      (of_eq (omega_rename w s) (carry hw)) (of_eq (empty_rename z s) (carry hz))
      (of_eq (SyntaxVariableSyntax.code_rename true w z head s) (carry hh))
      (of_eq (SyntaxTermSyntax.term_rename w c d P s) (carry hp))
      (of_eq (StructuralListFieldSyntax.field_rename w K z P s) (carry hK)) hM1 (.conjR hE)
      (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H a f c d q Y s) (carry hY))
    have directProof : Derives Ξ (direct (s w) (s c) (s f) (s d) (s P) (s H) (v 0).castSucc (v 1).castSucc (s Y)) := by
      apply Derives.exI V
      exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxForestSyntax.forest_rename,
        SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) (.conjI (.conjR hE) h)
    have res : Derives Ξ (result order R (s w) (s c) (s f) (s d) (s P) (s H) (s a) (s head) (s q) (s Y)) := by
      apply HornBinderRules.intro_many 4 _ (fun i => (v i).castSucc)
      exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]; rfl) (.conjI hM1 directProof)
    exact of_eq (result_rename order R (r w) (r c) (r f) (r d) (r P) (r H) (r a) (r head) (r q) (r Y) Fin.castSucc).symm res
  exact of_eq (result_rename order R w c f d P H a head q Y r).symm hResult
/-- Specialization when the actual target head is still bound zero. -/
theorem from_lifted {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (order : Bool) (R : Source.Formula (k+2))
    (w z a f c d K H head q Y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hh : Derives Γ (SyntaxVariableSyntax.code true w z head))
    (ha : Derives Γ (.mem z a))
    (hK : Derives Γ (StructuralListFieldSyntax.field w K z head))
    (hq : Derives Γ (ForcingGuardCode.compiled order R w a f head q))
    (hY : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H a f c d q Y)) :
    Derives Γ (result order R w c f d head H a head q Y) :=
  from_lifted_at hZ order R w z a f c d K H head head q Y hw hz hh ha hK hq hY

theorem from_instance {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (order : Bool) (Reln : Source.Formula (k+2))
    (w mode z a f T A C R S K H P r s u head q U Y : Fin m)
    (hf : Derives Γ (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s))
    (hh : Derives Γ (SyntaxMixedImageHead.head w A f u head))
    (hc : Derives Γ (ForcingGuardCode.compiled order Reln w A f head q))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q U))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P U Y)) :
    Derives Γ (result order Reln w z f T P S A head q Y) := by
  have heq := OmegaUniversal.empty_unique u z (ZFContext.arithmetic hZ).base.extensionality (.conjL hh) (Derives.conjL (Derives.conjR (Derives.conjR hf)))
  have hx := SyntaxVariableImagePoint.code_subst_index true w u head z heq (.conjL (.conjR hh))
  have ht := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have hcode := Derives.impE (.conjL (SyntaxTopFormulaCodes.instantiate_at_codes hZ w z T C P U Y r s (.conjL hf) ht)) hi
  exact from_compiled hZ order Reln w mode z a f T A C R S K H P r s head q U Y hf hx hc ho hcode

def input {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s u head q U Y : Fin m) : Formula m :=
  (ForcingMemberGuardOpening.frame w mode z a f T A C R S K H P r s).conj ((SyntaxMixedImageHead.head w A f u head).conj
    ((ForcingGuardCode.compiled order Reln w A f head q).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T q U).conj
        (SyntaxTopFormulaSyntax.instantiated w z T C P U Y))))
def sentence {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s u head q U Y : Fin m) : Source.Sentence :=
  ((input order Reln w mode z a f T A C R S K H P r s u head q U Y).imp (result order Reln w z f T P S A head q Y)).close

theorem kernel_certificate {k m} (order : Bool) (Reln : Source.Formula (k+2)) (w mode z a f T A C R S K H P r s u head q U Y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence order Reln w mode z a f T A C R S K H P r s u head q U Y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := input order Reln w mode z a f T A C R S K H P r s u head q U Y
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact from_instance (ZFContext.add (ZFContext.source_ZF m) E) order Reln w mode z a f T A C R S K H P r s u head q U Y
    (Derives.conjL h) (Derives.conjL (Derives.conjR h)) (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h)))) (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))

end PPAC.Migration.ForcingGuardOpening
