import PPAC.Migration.ForcingBinderInstantiation
import PPAC.Migration.ForcingFormulaInduction
import PPAC.Migration.Internal.SyntaxIdentityInduction
import PPAC.Migration.Internal.IndexFormulaRenameBridge

/-! One actual lifted opening followed by native instantiation equals the
original mixed substitution with the prefixed closed bound table. The
identity maps used to specialize the EXISTING full internal cancellation
are constructed in the object theory, including for nonstandard scopes. -/
namespace PPAC.Migration.ForcingBinderFormula
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem identity_term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b I J R S x u : Fin m) (hw : Derives Γ (omega w))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b a b))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b a b x u)) :
    Derives Γ (.equal x u) := by
  let B := (SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc a.castSucc I.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hI
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hJ1 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w b J Fin.castSucc) (under hJ B)
  let E := (SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc b.castSucc.castSucc J.castSucc.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last (m+1)))
  let Ξ := Context.add E (Context.image Formula.raise Δ)
  apply Derives.exE (p := E) hJ1
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hB2 : Derives Ξ ((SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc a.castSucc.castSucc I.castSucc.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last m).castSucc)) := of_eq
    (by simp only [B, Formula.raise, Formula.rename, SyntaxMapCodeSyntax.encoded_rename, SyntaxRenameTermIdentity.diagonal_rename]) (under hB E)
  have hZ2 := ZFContext.under (ZFContext.under hZ B) E
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw B) E)
  have he2 : Derives Ξ (IndexTermImageCodeSyntax.environment w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, IndexTermImageCodeSyntax.environment_rename]) (under (under he B) E)
  have hq2 : Derives Ξ (SyntaxCodedMixedTermSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc x.castSucc.castSucc u.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxCodedMixedTermSyntax.substituted_rename]) (under (under hq B) E)
  have hp := Derives.impE (Derives.conjR (TermTransformProgramCorrectness.checked_iff hZ2
    w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
    x.castSucc.castSucc u.castSucc.castSucc hw2)) hq2
  have hr := Derives.impE (Derives.conjL (IndexTermImageEnvironment.term_program_iff hZ2
    w.castSucc.castSucc I.castSucc.castSucc J.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) x.castSucc.castSucc u.castSucc.castSucc hw2 he2 (Derives.conjL hB2) (Derives.conjL hE))) hp
  exact SyntaxRenameTermIdentity.identity hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    a.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc x.castSucc.castSucc u.castSucc.castSucc
    hw2 (Derives.conjR hB2) (Derives.conjR hE) hr

private theorem term_input {m} {Γ : Context m} (w R S a b c d x y u : Fin m)
    (he : Derives Γ (.equal x y))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x u)) :
    Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y u) := by
  let F := SyntaxCodedMixedTermSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) u.castSucc
  have h0 : Derives Γ (F.instantiate x) := of_eq
    (by simp only [F, Formula.instantiate, SyntaxCodedMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq
  exact of_eq
    (by simp only [F, Formula.instantiate, SyntaxCodedMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.eqSubst F he h0)


private theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D I J B F : Fin m)
    (hf : Derives Γ (ForcingBinderInstantiation.frame w z a f T A C R S K H P r s D))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J B F A f A f)) :
    Derives Γ (ForcingTermDiagram.diagram w (four A A C z) (four f f T T)
      (four B K r D) (four F H s S)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let E := (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 B) (old 5 F) (old 5 A) (old 5 f) (old 5 A) (old 5 f) (slot 5 0) (slot 5 1)).conj
    ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 K) (old 5 H) (old 5 A) (old 5 f) (old 5 C) (old 5 T) (slot 5 1) (slot 5 2)).conj
      ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 r) (old 5 s) (old 5 C) (old 5 T) (old 5 z) (old 5 T) (slot 5 2) (slot 5 3)).conj
        (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 D) (old 5 S) (old 5 A) (old 5 f) (old 5 z) (old 5 T) (slot 5 0) (slot 5 4))))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ5 := HornBinderRules.zf_body 5 hZ E
  have hf5 : Derives Δ (ForcingBinderInstantiation.frame (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C)
    (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 D)) := of_eq
      (ForcingBinderInstantiation.frame_rename w z a f T A C R S K H P r s D (old 5)) (HornBinderRules.under_body 5 hf E)
  have hI5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w A I (old 5)) (HornBinderRules.under_body 5 hI E)
  have hJ5 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 5)) (HornBinderRules.under_body 5 hJ E)
  have he5 := of_eq (IndexTermImageCodeSyntax.environment_rename w I J B F A f A f (old 5)) (HornBinderRules.under_body 5 he E)
  have hEq := identity_term hZ5 (old 5 w) (old 5 A) (old 5 f) (old 5 I) (old 5 J) (old 5 B) (old 5 F)
    (slot 5 0) (slot 5 1) (Derives.conjL hf5) hI5 hJ5 he5 (Derives.conjL hE)
  have hFirst := term_input (old 5 w) (old 5 K) (old 5 H) (old 5 A) (old 5 f) (old 5 C) (old 5 T)
    (slot 5 1) (slot 5 0) (slot 5 2) (eq_symm hEq) (Derives.conjL (Derives.conjR hE))
  exact ForcingBinderInstantiation.term hZ5 (old 5 w) (old 5 z) (old 5 a) (old 5 f) (old 5 T) (old 5 A) (old 5 C)
    (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 P) (old 5 r) (old 5 s) (old 5 D)
    (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4) hf5
    (Derives.conjI hFirst (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR hE))) (Derives.conjR (Derives.conjR (Derives.conjR hE)))))

private theorem at_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D I J B F n u v y : Fin m)
    (hf : Derives Γ (ForcingBinderInstantiation.frame w z a f T A C R S K H P r s D))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J B F A f A f))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T n u))
    (h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T u v))
    (h3 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T n y)) :
    Derives Γ (.equal v y) := by
  have hw := Derives.conjL hf
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w D S A f z T n y hw h3
  have hi := SyntaxIdentityInduction.reflexive hZ w I J A f n hw hI hJ ht
  have h0 := Derives.impE (Derives.conjL (IndexFormulaRenameBridge.rename_iff hZ w I J B F A f A f n n hw he)) hi
  exact ForcingFormulaInduction.cancel hZ w (four A A C z) (four f f T T) (four B K r D) (four F H s S)
    n n u v y hw (term_diagram hZ w z a f T A C R S K H P r s D I J B F hf hI hJ he) h0 h1 h2 h3


/-- The three ACTUAL original mixed formula queries, with no candidate
identity code or desired output equality in the hypothesis. -/
def path {m} (w z f T A C S K H r s D n u v y : Fin m) : Formula m :=
  (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T n u).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w r s C T z T u v).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T n y))

theorem path_rename {m l} (w z f T A C S K H r s D n u v y : Fin m) (ρ : Fin m → Fin l) :
    (path w z f T A C S K H r s D n u v y).rename ρ =
      path (ρ w) (ρ z) (ρ f) (ρ T) (ρ A) (ρ C) (ρ S) (ρ K) (ρ H) (ρ r) (ρ s) (ρ D) (ρ n) (ρ u) (ρ v) (ρ y) := by
  simp only [path, Formula.rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D I J n u v y : Fin m)
    (hf : Derives Γ (ForcingBinderInstantiation.frame w z a f T A C R S K H P r s D))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (hp : Derives Γ (path w z f T A C S K H r s D n u v y)) : Derives Γ (.equal v y) := by
  have he := IndexTermImageEnvironment.exists_environment hZ w I J A f A f (Derives.conjL hf)
    (SyntaxIdentityCode.map_code w A I hI) (SyntaxIdentityCode.map_code w f J hJ)
  let E := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (old 2 A) (old 2 f) (old 2 A) (old 2 f)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hf2 := of_eq (ForcingBinderInstantiation.frame_rename w z a f T A C R S K H P r s D (old 2)) (HornBinderRules.under_body 2 hf E)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w A I (old 2)) (HornBinderRules.under_body 2 hI E)
  have hJ2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 2)) (HornBinderRules.under_body 2 hJ E)
  have hp2 := of_eq (path_rename w z f T A C S K H r s D n u v y (old 2)) (HornBinderRules.under_body 2 hp E)
  exact at_identity hZ2 (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 C)
    (old 2 R) (old 2 S) (old 2 K) (old 2 H) (old 2 P) (old 2 r) (old 2 s) (old 2 D)
    (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (old 2 n) (old 2 u) (old 2 v) (old 2 y)
    hf2 hI2 hJ2 hE (Derives.conjL hp2) (Derives.conjL (Derives.conjR hp2)) (Derives.conjR (Derives.conjR hp2))

/-- All internal formulas, including nonstandard codes and scopes. All four
auxiliary identity index/image codes are constructed and eliminated inside
ZF. This specializes existing full internal cancellation; no second formula
induction or syntax checker is introduced. -/
theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D n u v y : Fin m)
    (hf : Derives Γ (ForcingBinderInstantiation.frame w z a f T A C R S K H P r s D))
    (hp : Derives Γ (path w z f T A C S K H r s D n u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hf
  have hl := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hf)))
  have hLists := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H hl
  have hi := SyntaxIdentityCode.exists_code hZ w A hw (Derives.conjL (Derives.conjL hLists))
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc A.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hi
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hf1 := of_eq (ForcingBinderInstantiation.frame_rename w z a f T A C R S K H P r s D Fin.castSucc) (under hf E)
  have hfw1 : Derives Δ (.mem f.castSucc w.castSucc) := under (Derives.conjL (Derives.conjR hLists)) E
  have hj := SyntaxIdentityCode.exists_code hZ1 w.castSucc f.castSucc hw1 hfw1
  let B := SyntaxIdentityMapSyntax.identityCode w.castSucc.castSucc f.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add B (Context.image Formula.raise Δ)
  apply Derives.exE (p := B) hj
  have hB : Derives Ξ B := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 B
  have hf2 := of_eq (ForcingBinderInstantiation.frame_rename w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc D.castSucc Fin.castSucc) (under hf1 B)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename w.castSucc A.castSucc (Fin.last m) Fin.castSucc) (under hE B)
  have hp2 : Derives Ξ (path w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc
    S.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc D.castSucc.castSucc n.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc y.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, path_rename]) (under (under hp E) B)
  exact at_codes hZ2 w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc A.castSucc.castSucc C.castSucc.castSucc
    R.castSucc.castSucc S.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc P.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc D.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc y.castSucc.castSucc hf2 hI2 hB hp2

def sentence {m} (w z a f T A C R S K H P r s D n u v y : Fin m) : Source.Sentence :=
  (((ForcingBinderInstantiation.frame w z a f T A C R S K H P r s D).conj
    (path w z f T A C S K H r s D n u v y)).imp (.equal v y)).close

theorem kernel_certificate {m} (w z a f T A C R S K H P r s D n u v y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z a f T A C R S K H P r s D n u v y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (ForcingBinderInstantiation.frame w z a f T A C R S K H P r s D).conj (path w z f T A C S K H r s D n u v y)
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact formula (ZFContext.add (ZFContext.source_ZF m) E) w z a f T A C R S K H P r s D n u v y (Derives.conjL h) (Derives.conjR h)


/-- Direct consumer of the SAME native InstantiateTop judgment used by the
preorder instance chain. Its two actual substitution environments are
object-eliminated; the prefixed table type follows from the real cons.
Neither an environment answer nor a table typing answer is supplied. -/
theorem native {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P D n u v y : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hLists : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z T R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H))
    (hc : Derives Γ (StructuralListSyntax.consCode w P R D))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T n u))
    (hi : Derives Γ (SyntaxTopFormulaSyntax.instantiated w z T C P u v))
    (h3 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T n y)) :
    Derives Γ (.equal v y) := by
  let E := SyntaxTopFormulaSyntax.instantiateState (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 P) (old 2 u) (old 2 v) (slot 2 0) (slot 2 1)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ hi
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw E)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz E)
  have hLists2 := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a f z T R S (old 2)) (HornBinderRules.under_body 2 hLists E)
  have hl2 := of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w R S a f z T A C K H (old 2)) (HornBinderRules.under_body 2 hl E)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w P R D (old 2)) (HornBinderRules.under_body 2 hc E)
  have h12 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H A f C T n u (old 2)) (HornBinderRules.under_body 2 h1 E)
  have h32 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w D S A f z T n y (old 2)) (HornBinderRules.under_body 2 h3 E)
  have htP := Derives.conjL (SyntaxTopCodedEnvironmentTyping.instantiate_input (old 2 w) (old 2 z) (old 2 T) (old 2 C) (old 2 P) (slot 2 0) (slot 2 1) (Derives.conjL hE))
  have hA := Derives.conjL (Derives.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted (old 2 w) (old 2 R) (old 2 S) (old 2 a) (old 2 f) (old 2 z) (old 2 T) (old 2 A) (old 2 C) (old 2 K) (old 2 H) hl2))
  have hD := TypedArgumentListConstruction.cons_list hZ2 (old 2 w) (old 2 a) (old 2 A) (old 2 z) (old 2 T) (old 2 P) (old 2 R) (old 2 D)
    hw2 htP (Derives.conjL hLists2) hc2 hA
  have hf : Derives Δ (ForcingBinderInstantiation.frame (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 C) (old 2 R) (old 2 S)
    (old 2 K) (old 2 H) (old 2 P) (slot 2 0) (slot 2 1) (old 2 D)) :=
    .conjI hw2 (.conjI hz2 (.conjI hLists2 (.conjI hl2 (.conjI (Derives.conjL hE) (.conjI hc2 hD)))))
  exact formula hZ2 (old 2 w) (old 2 z) (old 2 a) (old 2 f) (old 2 T) (old 2 A) (old 2 C) (old 2 R) (old 2 S)
    (old 2 K) (old 2 H) (old 2 P) (slot 2 0) (slot 2 1) (old 2 D) (old 2 n) (old 2 u) (old 2 v) (old 2 y)
    hf (.conjI h12 (.conjI (Derives.conjR hE) h32))

def nativeInput {m} (w z a f T A C R S K H P D n u v y : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxMixedImageCodeSyntax.termLists w a f z T R S).conj
    ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj
      ((StructuralListSyntax.consCode w P R D).conj
        ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A f C T n u).conj
          ((SyntaxTopFormulaSyntax.instantiated w z T C P u v).conj
            (SyntaxMixedFormulaJudgmentSyntax.substituted w D S A f z T n y)))))))

def nativeSentence {m} (w z a f T A C R S K H P D n u v y : Fin m) : Source.Sentence :=
  ((nativeInput w z a f T A C R S K H P D n u v y).imp (.equal v y)).close

theorem native_kernel_certificate {m} (w z a f T A C R S K H P D n u v y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (nativeSentence w z a f T A C R S K H P D n u v y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := nativeInput w z a f T A C R S K H P D n u v y
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact native (ZFContext.add (ZFContext.source_ZF m) E) w z a f T A C R S K H P D n u v y
    (Derives.conjL h)    (Derives.conjL (Derives.conjR h))    (Derives.conjL (Derives.conjR (Derives.conjR h)))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR h))))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h))))))    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR h)))))))

/-- Public access to the existing identity-term proof. The original private
proof is reused verbatim; no second identity argument or decoder is added. -/
theorem identity_term_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b I J R S x u : Fin m) (hw : Derives Γ (omega w))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b a b))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a b a b x u)) :
    Derives Γ (.equal x u) :=
  identity_term hZ w a b I J R S x u hw hI hJ he hq

end PPAC.Migration.ForcingBinderFormula
