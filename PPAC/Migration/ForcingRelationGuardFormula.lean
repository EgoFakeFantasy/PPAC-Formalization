import PPAC.Migration.ForcingRelationImages
import PPAC.Migration.ForcingBinderFormula
import PPAC.Migration.NativeProofQuotation

/-! Full formula cancellation for the ACTUAL original guard route from
SAME bare R source versus the generated argument-table route. The existing
all-internal formula cancellation and identity proofs are reused. No new
formula induction, checker, recursor or forcing truth premise is added. -/
namespace PPAC.Migration.ForcingRelationGuardFormula
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def four {m} (a b c d : Fin m) : Fin 4 → Fin m :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

def path {m} (w z f t c d B F V K B0 D n u v y : Fin m) : Formula m :=
  (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n y))

theorem path_rename {m l} (w z f t c d B F V K B0 D n u v y : Fin m) (ρ : Fin m → Fin l) :
    (path w z f t c d B F V K B0 D n u v y).rename ρ =
    path (ρ w) (ρ z) (ρ f) (ρ t) (ρ c) (ρ d) (ρ B) (ρ F) (ρ V) (ρ K) (ρ B0) (ρ D) (ρ n) (ρ u) (ρ v) (ρ y) := by
  simp only [path, Formula.rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem compare_with_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t g c d B F V K B0 D I J IB IF n u v y : Fin m)
    (hw : Derives Γ (omega w))
    (hI : Derives Γ (SyntaxIdentityMapSyntax.identityCode w z I))
    (hJ : Derives Γ (SyntaxIdentityMapSyntax.identityCode w f J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J IB IF z f z f))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t g n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t g c d u v))
    (h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n y))
    (compare : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {A : Formula m}, Derives Γ A → Derives Δ (A.rename r)) →
      ∀ x p q a : Fin l,
      Derives Δ (SyntaxCodedMixedTermSyntax.substituted (r w) (r B) (r F) (r z) (r f) (r t) (r g) x p) →
      Derives Δ (SyntaxCodedMixedTermSyntax.substituted (r w) (r V) (r K) (r t) (r g) (r c) (r d) p q) →
      Derives Δ (SyntaxCodedMixedTermSyntax.substituted (r w) (r B0) (r D) (r z) (r f) (r c) (r d) x a) →
      Derives Δ (.equal q a)) :
    Derives Γ (.equal v y) := by
  let bounds := four z z t c
  let bs := four f f g d
  let rs := four IB B V B0
  let ss := four IF F K D
  have diagram : Derives Γ (ForcingTermDiagram.diagram w bounds bs rs ss) := by
    apply OriginalUniversalBlock.intro_many 5
    apply Derives.impI
    let E := (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 IB) (old 5 IF)
      (old 5 z) (old 5 f) (old 5 z) (old 5 f) (slot 5 0) (slot 5 1)).conj
      ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 B) (old 5 F)
        (old 5 z) (old 5 f) (old 5 t) (old 5 g) (slot 5 1) (slot 5 2)).conj
        ((SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 V) (old 5 K)
          (old 5 t) (old 5 g) (old 5 c) (old 5 d) (slot 5 2) (slot 5 3)).conj
          (SyntaxCodedMixedTermSyntax.substituted (old 5 w) (old 5 B0) (old 5 D)
            (old 5 z) (old 5 f) (old 5 c) (old 5 d) (slot 5 0) (slot 5 4))))
    let Δ := Context.add E (raisedContext 5 Γ)
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hZ5 := HornBinderRules.zf_body 5 hZ E
    have lift {P : Formula m} (h : Derives Γ P) := HornBinderRules.under_body 5 h E
    have hEq := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 z) (old 5 f)
      (old 5 I) (old 5 J) (old 5 IB) (old 5 IF) (slot 5 0) (slot 5 1)
      (of_eq (omega_rename w (old 5)) (lift hw))
      (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w z I (old 5)) (lift hI))
      (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w f J (old 5)) (lift hJ))
      (of_eq (IndexTermImageCodeSyntax.environment_rename w I J IB IF z f z f (old 5)) (lift he))
      (.conjL hE)
    have hNative := SyntaxMixedFormulaAtomicSubst.term_source (old 5 w) (old 5 B) (old 5 F)
      (old 5 z) (old 5 f) (old 5 t) (old 5 g) (slot 5 1) (slot 5 2) (slot 5 0)
      (eq_symm hEq) (.conjL (.conjR hE))
    exact compare (old 5) hZ5 lift (slot 5 0) (slot 5 2) (slot 5 3) (slot 5 4)
      hNative (.conjL (.conjR (.conjR hE))) (.conjR (.conjR (.conjR hE)))
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B F z f t g n u hw h0
  have hi := SyntaxIdentityInduction.reflexive hZ w I J z f n hw hI hJ ht
  have hId := Derives.impE (.conjL (IndexFormulaRenameBridge.rename_iff hZ w I J IB IF z f z f n n hw he)) hi
  exact ForcingFormulaInduction.cancel hZ w bounds bs rs ss n n u v y hw diagram hId h0
    h1 h2


/-- Compare an actual two-step mixed substitution against a direct one.
The intermediate scopes may differ from the source scopes. The existing
formula cancellation consumes the three actual queries and the term proof. -/
theorem compare_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t g c d B F V K B0 D n u v y : Fin m)
    (hw : Derives Γ (omega w)) (hzW : Derives Γ (.mem z w)) (hf : Derives Γ (.mem f w))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t g n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t g c d u v))
    (h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n y))
    (compare : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {A : Formula m}, Derives Γ A → Derives Δ (A.rename r)) →
      ∀ x p q a : Fin l,
      Derives Δ (SyntaxCodedMixedTermSyntax.substituted (r w) (r B) (r F) (r z) (r f) (r t) (r g) x p) →
      Derives Δ (SyntaxCodedMixedTermSyntax.substituted (r w) (r V) (r K) (r t) (r g) (r c) (r d) p q) →
      Derives Δ (SyntaxCodedMixedTermSyntax.substituted (r w) (r B0) (r D) (r z) (r f) (r c) (r d) x a) →
      Derives Δ (.equal q a)) :
    Derives Γ (.equal v y) := by
  let out := Formula.equal v y
  refine NativeProofQuotation.eliminate_objects hZ 1
    (fun r x => SyntaxIdentityMapSyntax.identityCode (r w) (r z) (x 0))
    (SyntaxIdentityCode.exists_code hZ w z hw hzW) out ?_
  intro l Δ r x hZ1 lift hI
  have hw1 := of_eq (omega_rename w r) (lift hw)
  have hf1 : Derives Δ (.mem (r f) (r w)) := lift hf
  refine NativeProofQuotation.eliminate_objects hZ1 1
    (fun s xs => SyntaxIdentityMapSyntax.identityCode (s (r w)) (s (r f)) (xs 0))
    (SyntaxIdentityCode.exists_code hZ1 (r w) (r f) hw1 hf1) (out.rename r) ?_
  intro l' Δ' s ys hZ2 lift2 hJ
  let ρ := s ∘ r
  have hw2 := of_eq (omega_rename (r w) s) (lift2 hw1)
  have hI2 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename (r w) (r z) (x 0) s) (lift2 hI)
  have env := IndexTermImageEnvironment.exists_environment hZ2 (ρ w) (s (x 0)) (ys 0)
    (ρ z) (ρ f) (ρ z) (ρ f) hw2
    (SyntaxIdentityCode.map_code (ρ w) (ρ z) (s (x 0)) hI2)
    (SyntaxIdentityCode.map_code (ρ w) (ρ f) (ys 0) hJ)
  refine NativeProofQuotation.eliminate_objects hZ2 2 (fun a q =>
    IndexTermImageCodeSyntax.environment (a (ρ w)) (a (s (x 0))) (a (ys 0))
      (q 0) (q 1) (a (ρ z)) (a (ρ f)) (a (ρ z)) (a (ρ f))) env ((out.rename r).rename s) ?_
  intro l'' Δ'' a q hZ3 lift3 hEnv
  let σ := a ∘ ρ
  have carry {P : Formula m} (h : Derives Γ P) : Derives Δ'' (P.rename σ) := by
    simpa only [σ, ρ, SourceAlgebra.rename_comp, Function.comp_def] using lift3 (lift2 (lift h))
  have hI3 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename (ρ w) (ρ z) (s (x 0)) a) (lift3 hI2)
  have hJ3 := of_eq (SyntaxIdentityMapSyntax.identityCode_rename (ρ w) (ρ f) (ys 0) a) (lift3 hJ)
  have result := compare_with_identity hZ3 (σ w) (σ z) (σ f) (σ t) (σ g) (σ c) (σ d)
    (σ B) (σ F) (σ V) (σ K) (σ B0) (σ D) (a (s (x 0))) (a (ys 0)) (q 0) (q 1)
    (σ n) (σ u) (σ v) (σ y) (of_eq (omega_rename w σ) (carry hw)) hI3 hJ3 hEnv
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B F z f t g n u σ) (carry h0))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V K t g c d u v σ) (carry h1))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B0 D z f c d n y σ) (carry h2)) (by
      intro l3 Δ3 r3 hZ4 lift4 x0 p0 q0 a0 h0 h1 h2
      exact compare (r3 ∘ σ) hZ4
        (fun h => of_eq (SourceAlgebra.rename_comp _ σ r3) (lift4 (carry h))) x0 p0 q0 a0 h0 h1 h2)
  simpa only [out, σ, ρ, Formula.rename, SourceAlgebra.rename_comp, Function.comp_def] using result

private theorem compare_paths {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d B F V K B0 D n u v y : Fin m)
    (hw : Derives Γ (omega w)) (hzW : Derives Γ (.mem z w)) (hf : Derives Γ (.mem f w))
    (hP : Derives Γ (path w z f t c d B F V K B0 D n u v y))
    (compare : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {A : Formula m}, Derives Γ A → Derives Δ (A.rename r)) →
      ∀ x p q a : Fin l,
      Derives Δ (ForcingRelationImages.guardPath (r w) (r z) (r f) (r t) (r c) (r d)
        (r B) (r F) (r V) (r K) (r B0) (r D) x p q a) → Derives Δ (.equal q a)) :
    Derives Γ (.equal v y) := by
  exact compare_queries hZ w z f t f c d B F V K B0 D n u v y hw hzW hf
    (.conjL hP) (.conjL (.conjR hP)) (.conjR (.conjR hP))
    (fun r hz carry x p q a h0 h1 h2 => compare r hz carry x p q a (.conjI h0 (.conjI h1 h2)))

/-- ALL internal formulas, including nonstandard codes, with arbitrary
internal target scopes c,d. Four auxiliary identity codes/tables are
object-generated and eliminated. Existing full formula induction is used
unchanged; no formula output or guard truth is supplied as an answer. -/
theorem formula {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 n u v y : Fin m)
    (hF : Derives Γ (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hP : Derives Γ (path w z f t c d B F V K B0 D n u v y)) : Derives Γ (.equal v y) := by
  have hw := Derives.conjL hF
  have hz := Derives.conjL (.conjR hF)
  have hf := Derives.conjL (.conjR (.conjR hF))
  apply compare_paths hZ w z f t c d B F V K B0 D n u v y hw
    (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    (SyntaxNumerals.range hZ (k+2) w f hw hf) hP
  intro l Δ r hZ1 lift x p q a hPath
  exact ForcingRelationImages.guard_term hZ1 (r w) (r z) (r f) (r t) (r c) (r d) (r S) (r L)
    (r R) (r i) (r j) (r M) (r D) (r B) (r F) (r V) (r K) (r B0) x p q a
    (of_eq (ForcingRelationImages.guardFrame_rename (k := k) w z f t c d S L R i j M D B F V K r)
      (lift hF)) hPath

def sentence {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v y : Fin m) : Source.Sentence :=
  (((ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj
    (path w z f t c d B F V K B0 D n u v y)).imp (.equal v y)).close

theorem kernel_certificate {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (sentence (k := k) w z f t c d S L R i j M D B F V K B0 n u v y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj (path w z f t c d B F V K B0 D n u v y)
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact formula (ZFContext.add (ZFContext.source_ZF m) E) w z f t c d S L R i j M D B F V K B0 n u v y (.conjL h) (.conjR h)

/-- Consume the SAME source R quotation/native guard map/query generated
by ForcingRelationSource. No independent native query or output is supplied;
the original raw relation query in that source record is retained. -/
theorem from_source {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (leaf : Fin 3)
    (w z t A f N G X c d S P Q i j M D V K B0 v y : Fin m) (E : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hSource : Derives Γ (ForcingRelationSource.data R leaf w z t A f N G X E))
    (hd : Derives Γ (ForcingRelationImages.data n w f c d S P Q i j M D))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Derives Γ (ForcingReflexiveImages.replacement w f c d S j Q K))
    (hGuard : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d G v))
    (hCommon : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d X y)) : Derives Γ (.equal v y) := by
  have he := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hNative := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hF : Derives Γ (ForcingRelationImages.guardFrame (k := n) w z f t c d S P Q i j M D (E 2) (E 3) V K) :=
    .conjI hw (.conjI hz (.conjI hf (.conjI he (.conjI hd (.conjI hV hK)))))
  exact formula hZ w z f t c d S P Q i j M D (E 2) (E 3) V K B0 X G v y hF (.conjI hNative (.conjI hGuard hCommon))

/-- Turn the supplied comparison of actual term queries into the actual
direct substitution of the same formula. The direct output is generated.
The initial bound scope can be any internal natural. -/
theorem to_direct_at_scope {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d B F V K B0 D n u v : Fin m)
    (hw : Derives Γ (omega w)) (hzW : Derives Γ (.mem z w)) (hf : Derives Γ (.mem f w))
    (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z c d B0))
    (hD : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f c d D))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v))
    (compare : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {A : Formula m}, Derives Γ A → Derives Δ (A.rename r)) →
      ∀ x p q a : Fin l,
      Derives Δ (ForcingRelationImages.guardPath (r w) (r z) (r f) (r t) (r c) (r d)
        (r B) (r F) (r V) (r K) (r B0) (r D) x p q a) → Derives Δ (.equal q a)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v) := by
  let out := SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v
  have ht := SyntaxMixedFormulaJudgmentTyping.source_type hZ w B F z f t f n u hw h0
  have existsDirect := SyntaxMixedFormulaOutputInduction.actual_exists hZ w B0 D z f c d n hw
    (.conjI ht (.conjI hB0 hD))
  refine NativeProofQuotation.eliminate_objects hZ 1 (fun r q =>
    SyntaxMixedFormulaJudgmentSyntax.substituted (r w) (r B0) (r D) (r z) (r f) (r c) (r d) (r n) (q 0))
    existsDirect out ?_
  intro l Δ r q hZ1 lift hCandidate
  have h01 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B F z f t f n u r) (lift h0)
  have h11 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w V K t f c d u v r) (lift h1)
  have hEq := compare_paths hZ1 (r w) (r z) (r f) (r t) (r c) (r d) (r B) (r F) (r V) (r K)
    (r B0) (r D) (r n) (r u) (r v) (q 0) (of_eq (omega_rename w r) (lift hw))
    (lift hzW) (lift hf) (.conjI h01 (.conjI h11 hCandidate)) (by
      intro l' Δ' s hZ2 lift2 x p q a hPath
      exact compare (s ∘ r) hZ2
        (fun h => of_eq (SourceAlgebra.rename_comp _ r s) (lift2 (lift h))) x p q a hPath)
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w B0 D z f c d n v r).symm
    (SyntaxMixedFormulaJudgmentSubst.subst_q (r w) (r B0) (r D) (r z) (r f) (r c) (r d)
      (r n) (q 0) (r v) (eq_symm hEq) hCandidate)

/-- Empty-bound specialization used by the original bare-relation routes. -/
theorem to_direct_from_terms {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d B F V K B0 D n u v : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hf : Derives Γ (.mem f w))
    (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z c d B0))
    (hD : Derives Γ (SyntaxMixedImageCodeSyntax.termList w f c d D))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v))
    (compare : ∀ {l} {Δ : Context l} (r : Fin m → Fin l), ZFContext.Evidence Δ →
      (∀ {A : Formula m}, Derives Γ A → Derives Δ (A.rename r)) →
      ∀ x p q a : Fin l,
      Derives Δ (ForcingRelationImages.guardPath (r w) (r z) (r f) (r t) (r c) (r d)
        (r B) (r F) (r V) (r K) (r B0) (r D) x p q a) → Derives Δ (.equal q a)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v) :=
  to_direct_at_scope hZ w z f t c d B F V K B0 D n u v hw
    (OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz)
    hf hB0 hD h0 h1 compare

/-- Generate the common direct query INTERNALLY and rewrite its output
to the SAME actual guard output. No common query/output is an input. -/
theorem to_direct {k m : Nat} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z f t c d S L R i j M D B F V K B0 n u v : Fin m)
    (hF : Derives Γ (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K))
    (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z c d B0))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v) := by
  have hw := Derives.conjL hF
  have hz := Derives.conjL (.conjR hF)
  have hf := Derives.conjL (.conjR (.conjR hF))
  have hData := Derives.conjL (.conjR (.conjR (.conjR (.conjR hF))))
  have hD := ForcingRelationImages.target_type k w f c d S L R i j M D hData
  apply to_direct_from_terms hZ w z f t c d B F V K B0 D n u v hw hz
    (SyntaxNumerals.range hZ (k+2) w f hw hf) hB0 hD h0 h1
  intro l Δ r hZ1 lift x p q a hPath
  exact ForcingRelationImages.guard_term hZ1 (r w) (r z) (r f) (r t) (r c) (r d) (r S) (r L)
    (r R) (r i) (r j) (r M) (r D) (r B) (r F) (r V) (r K) (r B0) x p q a
    (of_eq (ForcingRelationImages.guardFrame_rename (k := k) w z f t c d S L R i j M D B F V K r)
      (lift hF)) hPath

/-- Actual common-source consumer, with no supplied common-query answer. -/
theorem from_source_to_direct {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (n+2)) (leaf : Fin 3)
    (w z t A f N G X c d S P Q i j M D V K B0 v : Fin m) (E : Fin 4 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (SyntaxNumeralSyntax.numeral 0 z))
    (hf : Derives Γ (SyntaxNumeralSyntax.numeral (n+2) f))
    (hSource : Derives Γ (ForcingRelationSource.data R leaf w z t A f N G X E))
    (hd : Derives Γ (ForcingRelationImages.data n w f c d S P Q i j M D))
    (hV : Derives Γ (SyntaxForestSyntax.forest 1 w (fun _ => P) V))
    (hK : Derives Γ (ForcingReflexiveImages.replacement w f c d S j Q K))
    (hB0 : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z c d B0))
    (hGuard : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d G v)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d X v) := by
  have he := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hNative := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hSource)))
  have hF : Derives Γ (ForcingRelationImages.guardFrame (k := n) w z f t c d S P Q i j M D (E 2) (E 3) V K) :=
    .conjI hw (.conjI hz (.conjI hf (.conjI he (.conjI hd (.conjI hV hK)))))
  exact to_direct hZ w z f t c d S P Q i j M D (E 2) (E 3) V K B0 X G v hF hB0 hNative hGuard

def directInput {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v : Fin m) : Formula m :=
  (ForcingRelationImages.guardFrame (k := k) w z f t c d S L R i j M D B F V K).conj
    ((SyntaxMixedImageCodeSyntax.termList w z c d B0).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w B F z f t f n u).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w V K t f c d u v)))

def directSentence {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v : Fin m) : Source.Sentence :=
  ((directInput (k := k) w z f t c d S L R i j M D B F V K B0 n u v).imp
    (SyntaxMixedFormulaJudgmentSyntax.substituted w B0 D z f c d n v)).close

theorem direct_kernel_certificate {k m : Nat} (w z f t c d S L R i j M D B F V K B0 n u v : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (directSentence (k := k) w z f t c d S L R i j M D B F V K B0 n u v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := directInput (k := k) w z f t c d S L R i j M D B F V K B0 n u v
  let Γ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Γ E := .hyp (Or.inl rfl)
  exact to_direct (ZFContext.add (ZFContext.source_ZF m) E) w z f t c d S L R i j M D B F V K B0 n u v
    (Derives.conjL h) (Derives.conjL (Derives.conjR h))
    (Derives.conjL (Derives.conjR (Derives.conjR h))) (Derives.conjR (Derives.conjR (Derives.conjR h)))

end PPAC.Migration.ForcingRelationGuardFormula
