import PPAC.Migration.ForcingGuardDiagram

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
