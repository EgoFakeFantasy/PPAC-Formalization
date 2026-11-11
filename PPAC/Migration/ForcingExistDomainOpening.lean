import PPAC.Migration.ForcingExistDomainSource
import PPAC.Migration.ForcingExistDomainImages
import PPAC.Migration.ForcingExistChildOpening
import PPAC.Migration.ForcingRelationImages

/-! Actual domain compiler and TWO real openings versus the SAME bare H
canonical arguments. Runtime source depths and target d/T remain internal;
finite H/k describe the pinned fixed domain guard only. Original full formula
cancellation, native quotation, closed-term and zero-field proofs are reused. -/
namespace PPAC.Migration.ForcingExistDomainOpening
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

def frame {m} (k : Nat) (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxMixedImageCodeSyntax.termLists w a f z T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A c K H).conj ((SyntaxCodedMixedBinderSyntax.lifted w K H A f c T B d L M).conj ((ForcingReflexiveImages.replacement w f d T Base j p S).conj ((SyntaxNumeralSyntax.numeral k I).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxVariableSyntax.code true w z x).conj ((SyntaxMixedImageHead.head w d T z Name).conj (ForcingExistDomainImages.data k w f j d T Base I Name Whole Img D)))))))))))
theorem frame_rename {m l} (k : Nat) (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D : Fin m) (ρ : Fin m → Fin l) :
    (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D).rename ρ = frame k (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ T) (ρ c) (ρ d) (ρ R) (ρ S) (ρ K) (ρ H) (ρ L) (ρ M) (ρ Base) (ρ I) (ρ j) (ρ p) (ρ x) (ρ Name) (ρ Whole) (ρ Img) (ρ D) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, SyntaxMixedImageCodeSyntax.termLists_rename,
    SyntaxCodedMixedBinderSyntax.lifted_rename, ForcingReflexiveImages.replacement_rename,
    SyntaxNumeralSyntax.numeral_rename, SyntaxVariableSyntax.code_rename, SyntaxMixedImageHead.head_rename, ForcingExistDomainImages.data_rename]

def rows {k m} (Dom : Source.Formula (k+1)) (w z B f j x Nraw : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m) : Formula m :=
  (ForcingGuardCode.matrix true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw v).conj
    (ForcingExistDomainSource.data Dom w z (v 0) f j (v 1) (s 0) (s 1) (s 2))
theorem rows_rename {k m l} (Dom : Source.Formula (k+1)) (w z B f j x Nraw : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (rows Dom w z B f j x Nraw v s).rename ρ = rows Dom (ρ w) (ρ z) (ρ B) (ρ f) (ρ j) (ρ x) (ρ Nraw) (fun i => ρ (v i)) (fun i => ρ (s i)) := by
  simp only [rows, Formula.rename, ForcingGuardCode.matrix_rename, ForcingExistDomainSource.data_rename]

def path {m} (w z B f j d T L M D n q r y o : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w (s 1) (s 2) z j (v 0) f n q).conj
    ((SyntaxCodedMixedTermSyntax.substituted w (v 2) (v 3) (v 0) f B f q r).conj
      ((SyntaxCodedMixedTermSyntax.substituted w L M B f d T r y).conj
        (SyntaxCodedMixedTermSyntax.substituted w (s 1) D z j d T n o)))
theorem path_rename {m l} (w z B f j d T L M D n q r y o : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m) (ρ : Fin m → Fin l) :
    (path w z B f j d T L M D n q r y o v s).rename ρ =
      path (ρ w) (ρ z) (ρ B) (ρ f) (ρ j) (ρ d) (ρ T) (ρ L) (ρ M) (ρ D) (ρ n) (ρ q) (ρ r) (ρ y) (ρ o) (fun i => ρ (v i)) (fun i => ρ (s i)) := by
  simp only [path, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

private structure Inputs {k m} (Γ : Context m) (Dom : Source.Formula (k+1)) (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hf : Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D)
  hr : Derives Γ (rows Dom w z B f j x Nraw v s)
  hp : Derives Γ (path w z B f j d T L M D n q r y o v s)

private theorem Inputs.add {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) (E : Formula m) : Inputs (Context.add E Γ) Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s :=
  ⟨ZFContext.add h.zf E, SourceLogic.add h.hf E, SourceLogic.add h.hr E, SourceLogic.add h.hp E⟩
private theorem Inputs.in_body {k m t} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) (E : Formula (m+t)) :
    Inputs (Context.add E (raisedContext t Γ)) Dom (old t w) (old t z) (old t a) (old t A) (old t B) (old t f) (old t T) (old t c) (old t d) (old t R) (old t S) (old t K) (old t H) (old t L) (old t M) (old t Base) (old t I) (old t j) (old t p) (old t x) (old t Name) (old t Whole) (old t Img) (old t D) (old t Nraw) (old t n) (old t q) (old t r) (old t y) (old t o) (fun i => old t (v i)) (fun i => old t (s i)) :=
  ⟨HornBinderRules.zf_body t h.zf E,
    of_eq (frame_rename k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D (old t)) (HornBinderRules.under_body t h.hf E),
    of_eq (rows_rename Dom w z B f j x Nraw v s (old t)) (HornBinderRules.under_body t h.hr E),
    of_eq (path_rename w z B f j d T L M D n q r y o v s (old t)) (HornBinderRules.under_body t h.hp E)⟩
private theorem Inputs.hw {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (omega w) := (Derives.conjL (h.hf))
private theorem Inputs.zero {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (empty z) := (Derives.conjL (Derives.conjR (h.hf)))
private theorem Inputs.closed {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a f z T R S) := (Derives.conjL (Derives.conjR (Derives.conjR (h.hf))))
private theorem Inputs.lift1 {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A c K H) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))
private theorem Inputs.lift2 {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w K H A f c T B d L M) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))))
private theorem Inputs.replacement {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (ForcingReflexiveImages.replacement w f d T Base j p S) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))))
private theorem Inputs.isI {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxNumeralSyntax.numeral k I) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))))))
private theorem Inputs.isJ {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxNumeralSyntax.numeral (k+1) j) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))))))
private theorem Inputs.isF {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxNumeralSyntax.numeral (k+2) f) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))))))))
private theorem Inputs.sourceHead {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxVariableSyntax.code true w z x) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf)))))))))))
private theorem Inputs.nameHead {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (SyntaxMixedImageHead.head w d T z Name) := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))))))))))
private theorem Inputs.images {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (ForcingExistDomainImages.data k w f j d T Base I Name Whole Img D) := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (h.hf))))))))))))

private theorem name_point {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) (i : Fin m) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hx : Derives Γ (SyntaxVariableSyntax.code false w i n)) : Derives Γ (.equal y o) := by
  have h0 := Derives.conjL h.hp
  have h1 := Derives.conjL (.conjR h.hp)
  have h2 := Derives.conjL (.conjR (.conjR h.hp))
  have h3 := Derives.conjR (.conjR (.conjR h.hp))
  have hNative := Derives.conjL (.conjR (.conjR h.hr))
  have hQ := ForcingRelationImages.mapped_variable_arity h.zf (ForcingExistDomainSource.arguments k) (Fin.last k)
    w z j (v 0) f (s 1) (s 2) i n q h.hw hNative hi hx h0
  have hQtree : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 0 [PureSyntaxQuotation.Original.leaf 0]) w q) :=
    of_eq (by simp only [ForcingExistDomainSource.arguments, Fin.lastCases_last, PureQuotationSyntax.term, PureSyntaxQuotation.termTree]; rfl) hQ
  have hq0 := OriginalQuotationVariableFields.variable_of_tree h.zf true 0 w z q h.hw h.zero hQtree
  have hMid := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w (v 2) (v 3) (v 0) f B f q r z h.hw
    (.conjL (SyntaxCodedMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ h1)) hq0)) h1
  have hForest := Derives.conjL (.conjR (.conjR (.conjL h.hr)))
  have hrx := Derives.impE (.conjL (SyntaxForestFieldValues.field_at h.zf 1 w (fun _ => x) (v 2) 0 z r h.hw hForest h.zero)) (.conjR hMid)
  have h2x := SyntaxMixedFormulaAtomicSubst.term_source w L M B f d T r y x hrx h2
  have hY := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf true w L M B f d T x y z h.hw
    (SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h.lift2) h.sourceHead)) h2x
  have hy0 := Derives.impE (.conjL (ForcingExistChildOpening.zero_fields h.zf w z K H A f c T B d L M y h.hw h.zero h.lift2)) hY
  have hyName := SyntaxVariables.unique h.zf true w z y Name h.hw hy0 (.conjL (.conjR h.nameHead))
  have hO := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w (s 1) D z j d T n o i h.hw
    (.conjL (SyntaxCodedMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ h3)) hx)) h3
  have hCases := Derives.impE (.conjL (ForcingExistDomainImages.field_iff h.zf w f j d T Base I Name Whole Img D i o h.images (.conjL hO))) (.conjR hO)
  have he := SyntaxNumerals.unique h.zf k i I hi h.isI
  have hoName : Derives Γ (.equal o Name) := by
    apply Derives.disjE hCases
    · exact .conjR (.hyp (Or.inl rfl))
    · exact .botE (.impE (.conjL (.hyp (Or.inl rfl))) (add he _))
  exact eq_trans hyName (eq_symm hoName)

private theorem parameter_point {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) (p0 : Fin k) (i : Fin m)
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral p0.val i)) (hx : Derives Γ (SyntaxVariableSyntax.code false w i n)) : Derives Γ (.equal y o) := by
  have h0 := Derives.conjL h.hp
  have h1 := Derives.conjL (.conjR h.hp)
  have h2 := Derives.conjL (.conjR (.conjR h.hp))
  have h3 := Derives.conjR (.conjR (.conjR h.hp))
  have hNative := Derives.conjL (.conjR (.conjR h.hr))
  have hQ := ForcingRelationImages.mapped_variable_arity h.zf (ForcingExistDomainSource.arguments k) p0.castSucc
    w z j (v 0) f (s 1) (s 2) i n q h.hw hNative hi hx h0
  have hIndex : (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable p0.castSucc.castSucc).index = p0.val :=
    ProjectNativeRenaming.variable_index (fun _ : Fin 1 => p0.castSucc.castSucc)
      (YesMetaZFC.SetTheory.Definitional.Project.fo_bound_variable (0 : Fin 1))
  have hQtree : Derives Γ (OriginalTreeQuotationSyntax.tree (.node 1 [PureSyntaxQuotation.Original.leaf p0.val]) w q) :=
    of_eq (by simp only [ForcingExistDomainSource.arguments, Fin.lastCases_castSucc, PureQuotationSyntax.term, PureSyntaxQuotation.termTree, hIndex]) hQ
  have hqI := OriginalQuotationVariableFields.variable_of_tree h.zf false p0.val w i q h.hw hi hQtree
  have hMid := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w (v 2) (v 3) (v 0) f B f q r i h.hw
    (.conjL (SyntaxCodedMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ h1)) hqI)) h1
  have hIdentity := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjL h.hr)))))
  have hrI := ForcingMemberGuard.identity_field h.zf w B f (v 3) i r hIdentity (.conjL hMid) (.conjR hMid)
  have hY := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w L M B f d T r y i h.hw
    (SyntaxCodedMixedBinderTyping.output_lists _ _ _ _ _ _ _ _ _ _ _ h.lift2) hrI)) h2
  have hO := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h.zf false w (s 1) D z j d T n o i h.hw
    (.conjL (SyntaxCodedMixedTermTyping.input_of_substituted _ _ _ _ _ _ _ _ _ h3)) hx)) h3
  have hCases := Derives.impE (.conjL (ForcingExistDomainImages.field_iff h.zf w f j d T Base I Name Whole Img D i o h.images (.conjL hO))) (.conjR hO)
  have hneI := SyntaxNumerals.different h.zf p0.val k (Nat.ne_of_lt p0.isLt) i I hi h.isI
  have hBase : Derives Γ (field w Base i o) := by
    apply Derives.disjE hCases
    · exact .botE (.impE (add hneI _) (.conjL (.hyp (Or.inl rfl))))
    · exact .conjR (.hyp (Or.inl rfl))
  have hif := SyntaxNumeralMembers.index_member h.zf (k+2) p0.castSucc.castSucc f i h.isF hi
  have hneJ := SyntaxNumerals.different h.zf p0.val (k+1) (Nat.ne_of_lt (Nat.lt_trans p0.isLt (Nat.lt_succ_self k))) i j hi h.isJ
  have hS := Derives.impE (.conjR (ForcingReflexiveImages.field_iff w f d T Base j p S i o h.replacement hif)) (.disjR (.conjI hneJ hBase))
  have hTerm := SyntaxMixedImageCodeFields.field_type w f z T S i o (.conjR h.closed) hif hS
  have hClosed := InstantiateOperationFrameSyntax.intro_closedParameter w T o z h.zero hTerm
  have hs : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  have hFirst := Derives.impE (.conjR (ForcingExistChildOpening.closed_fields h.zf false w R S a f z T A c K H i i o o h.hw h.lift1 hif hS hs hClosed)) (.eqRefl o)
  exact Derives.impE (.conjL (ForcingExistChildOpening.closed_fields h.zf false w K H A f c T B d L M i i o y h.hw h.lift2 (.conjL hFirst) (.conjR hFirst) hs hClosed)) hY

private theorem term_from_inputs {k m} {Γ : Context m} {Dom : Source.Formula (k+1)} {w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m} {v : Fin 4 → Fin m} {s : Fin 3 → Fin m}
    (h : Inputs Γ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o v s) : Derives Γ (.equal y o) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w (s 1) (s 2) z j (v 0) f n q (.conjL h.hp)
  apply Derives.disjE (.conjR ht)
  · let E := SyntaxTermSyntax.branch true w z n
    let Q := SyntaxTermSyntax.branchWitness true w z n
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w z n _ (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have h1 := (h.add E).in_body Q
    exact .botE (.impE (OmegaSyntax.empty_at z.castSucc (Fin.last m) h1.zero) (.conjL hQ))
  · let E := SyntaxTermSyntax.branch false w j n
    let Q := SyntaxTermSyntax.branchWitness false w j n
    let Δ := Context.add Q (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w j n _ (.hyp (Or.inl rfl))
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have h1 := (h.add E).in_body Q
    have hb := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff h1.zf (k+1) j.castSucc (Fin.last m) h1.isJ)) (.conjL hQ)
    have hc := SyntaxPositionSyntax.below_imp (k+1) (Fin.last m) (.equal y.castSucc o.castSucc) (fun index => by
      apply Derives.impI
      exact Fin.lastCases
        (name_point (h1.add _) (Fin.last m) (.hyp (Or.inl rfl)) (add (.conjR hQ) _))
        (fun p0 => parameter_point (h1.add _) p0 (Fin.last m) (.hyp (Or.inl rfl)) (add (.conjR hQ) _)) index)
    exact .impE hc hb

theorem term {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw n q r y o : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m)
    (hf : Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D)) (hr : Derives Γ (rows Dom w z B f j x Nraw v s))
    (hp : Derives Γ (path w z B f j d T L M D n q r y o v s)) : Derives Γ (.equal y o) :=
  term_from_inputs ⟨hZ, hf, hr, hp⟩


private def four {α : Type} (a b c d : α) : Fin 4 → α := Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

private theorem term_diagram {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m)
    (hf : Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D)) (hr : Derives Γ (rows Dom w z B f j x Nraw v s)) :
    Derives Γ (ForcingTermDiagram.diagram w (four z (v 0) B d) (four j f f T)
      (four (s 1) (v 2) L (s 1)) (four (s 2) (v 3) M D)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let E := path (old 5 w) (old 5 z) (old 5 B) (old 5 f) (old 5 j) (old 5 d) (old 5 T) (old 5 L) (old 5 M) (old 5 D)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (v i)) (fun i => old 5 (s i))
  let Δ := Context.add E (raisedContext 5 Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  exact term (HornBinderRules.zf_body 5 hZ E) Dom (old 5 w) (old 5 z) (old 5 a) (old 5 A) (old 5 B) (old 5 f) (old 5 T) (old 5 c) (old 5 d) (old 5 R) (old 5 S) (old 5 K) (old 5 H) (old 5 L) (old 5 M) (old 5 Base) (old 5 I) (old 5 j) (old 5 p) (old 5 x) (old 5 Name) (old 5 Whole) (old 5 Img) (old 5 D) (old 5 Nraw)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4) (fun i => old 5 (v i)) (fun i => old 5 (s i))
    (of_eq (frame_rename k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D (old 5)) (HornBinderRules.under_body 5 hf E))
    (of_eq (rows_rename Dom w z B f j x Nraw v s (old 5)) (HornBinderRules.under_body 5 hr E)) hE

/-- SAME original H source query, complete domain compiler and TWO actual
openings, specialized into the EXISTING full internal formula cancellation. -/
theorem formula {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw Y O : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m)
    (hf : Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D)) (hr : Derives Γ (rows Dom w z B f j x Nraw v s))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M B f d T Nraw Y))
    (hd : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (s 1) D z j d T (s 0) O)) : Derives Γ (.equal Y O) := by
  have h0 := Derives.conjR (.conjR (.conjR hr))
  have h1 := Derives.conjR (.conjR (.conjR (.conjR (.conjR (.conjL hr)))))
  exact ForcingFormulaInduction.cancel hZ w (four z (v 0) B d) (four j f f T)
    (four (s 1) (v 2) L (s 1)) (four (s 2) (v 3) M D) (s 0) (v 1) Nraw Y O (.conjL hf)
    (term_diagram hZ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw v s hf hr) h0 h1 ho hd

/-- Produce/erase the direct candidate internally. The canonical query has
the SAME actual raw output; no queried code/equality is supplied as an answer. -/
theorem query {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw Y : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m)
    (hf : Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D)) (hr : Derives Γ (rows Dom w z B f j x Nraw v s))
    (ho : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M B f d T Nraw Y)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w (s 1) D z j d T (s 0) Y) := by
  have hw := Derives.conjL hf
  have hz := Derives.conjL (.conjR hf)
  have hImage := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))))
  have hTarget := ForcingExistDomainImages.target_type w f j d T Base I Name Whole Img D hImage
  have hBound := Derives.conjL (Derives.conjR (Derives.conjL (Derives.conjR (.conjR hr))))
  have hNil : Derives Γ (SyntaxMixedImageCodeSyntax.termList w z d T (s 1)) :=
    .conjI (.conjL hBound) (.conjI (.conjL (.conjR hTarget)) (.conjI (.conjL (.conjR (.conjR hBound)))
      (TypedArgumentListConstruction.nil_typed_fields w z d T (s 1) hz)))
  have hType := SyntaxMixedFormulaJudgmentTyping.source_type hZ w (s 1) (s 2) z j (v 0) f (s 0) (v 1) hw (.conjR (.conjR (.conjR hr)))
  let E := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (s 1).castSucc D.castSucc z.castSucc j.castSucc d.castSucc T.castSucc (s 0).castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w (s 1) D z j d T (s 0) hw (.conjI hType (.conjI hNil hTarget)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hf1 := of_eq (frame_rename k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Fin.castSucc) (under hf E)
  have hr1 := of_eq (rows_rename Dom w z B f j x Nraw v s Fin.castSucc) (under hr E)
  have ho1 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L M B f d T Nraw Y Fin.castSucc) (under ho E)
  have he := formula (ZFContext.under hZ E) Dom w.castSucc z.castSucc a.castSucc A.castSucc B.castSucc f.castSucc T.castSucc c.castSucc d.castSucc R.castSucc S.castSucc K.castSucc H.castSucc L.castSucc M.castSucc Base.castSucc I.castSucc j.castSucc p.castSucc x.castSucc Name.castSucc Whole.castSucc Img.castSucc D.castSucc Nraw.castSucc Y.castSucc (Fin.last m) (fun i => (v i).castSucc) (fun i => (s i).castSucc) hf1 hr1 ho1 hE
  have hOut := SyntaxMixedFormulaJudgmentSubst.subst_q w.castSucc (s 1).castSucc D.castSucc z.castSucc j.castSucc d.castSucc T.castSucc (s 0).castSucc (Fin.last m) Y.castSucc (eq_symm he) hE
  exact of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w (s 1) D z j d T (s 0) Y Fin.castSucc).symm hOut

private theorem compare_at_rows {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw Y R1 S1 K1 H1 L1 M1 q Y1 : Fin m) (v : Fin 4 → Fin m) (s : Fin 3 → Fin m)
    (hf : Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D))
    (hg : Derives Γ (frame k w z a A B f T c d R1 S1 K1 H1 L1 M1 Base I j q x Name Whole Img D))
    (hr : Derives Γ (rows Dom w z B f j x Nraw v s))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M B f d T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 B f d T Nraw Y1)) : Derives Γ (.equal Y Y1) := by
  have h0 := query hZ Dom w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw Y v s hf hr hy
  have h1 := query hZ Dom w z a A B f T c d R1 S1 K1 H1 L1 M1 Base I j q x Name Whole Img D Nraw Y1 v s hg hr hy1
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (s 1) D z j d T (s 0) Y Y1 (.conjL hf) h0 h1


private theorem compare_at_images {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D Nraw Y R1 S1 K1 H1 L1 M1 q Nraw1 Y1 : Fin m)
    (hf : Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D))
    (hg : Derives Γ (frame k w z a A B f T c d R1 S1 K1 H1 L1 M1 Base I j q x Name Whole Img D))
    (hc : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M B f d T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 B f d T Nraw1 Y1)) : Derives Γ (.equal Y Y1) := by
  have he := ForcingGuardCode.unique hZ true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw Nraw1 (.conjL hf) hc hd
  let P := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc L1.castSucc M1.castSucc B.castSucc f.castSucc d.castSucc T.castSucc (Fin.last m) Y1.castSucc
  have hy1' : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 B f d T Nraw Y1) :=
    of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (Derives.eqSubst P (eq_symm he) (of_eq (by simp only [P, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hy1))
  have hp := ForcingExistDomainSource.from_compiled hZ Dom w z B f j x Nraw (.conjL hf) (.conjL (.conjR hf)) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))) (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))))) hc
  let O := ForcingExistDomainSource.compilerBody Dom w z B f j x Nraw
  let Δ := Context.add O (raisedContext 4 Γ)
  apply HornBinderRules.eliminate_many 4 O _ hp
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  let C := ForcingExistDomainSource.body Dom (old 4 w) (old 4 z) (slot 4 0) (old 4 f) (old 4 j) (slot 4 1)
  let Ξ := Context.add C (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 C _ (.conjR hO)
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hMatrix : Derives Ξ (ForcingGuardCode.matrix true (ForcingExistGuardsCode.domainOrder Dom) (old 7 w) (old 7 B) (old 7 f) (old 7 x) (old 7 Nraw) (fun i => old 3 (slot 4 i))) :=
    of_eq (by simp only [ForcingGuardCode.matrix_rename]; rfl) (HornBinderRules.under_body 3 (.conjL hO) C)
  have hr7 : Derives Ξ (rows Dom (old 7 w) (old 7 z) (old 7 B) (old 7 f) (old 7 j) (old 7 x) (old 7 Nraw) (fun i => old 3 (slot 4 i)) (slot 3)) := .conjI hMatrix hC
  have hf7 := of_eq (by simp only [frame_rename]; rfl) (HornBinderRules.under_body 3 (HornBinderRules.under_body 4 hf O) C)
  have hg7 := of_eq (by simp only [frame_rename]; rfl) (HornBinderRules.under_body 3 (HornBinderRules.under_body 4 hg O) C)
  have hy7 := of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 3 (HornBinderRules.under_body 4 hy O) C)
  have hy17 := of_eq (by simp only [SyntaxMixedFormulaJudgmentSyntax.substituted_rename]; rfl) (HornBinderRules.under_body 3 (HornBinderRules.under_body 4 hy1' O) C)
  exact compare_at_rows (HornBinderRules.zf_body 3 (HornBinderRules.zf_body 4 hZ O) C) Dom (old 7 w) (old 7 z) (old 7 a) (old 7 A) (old 7 B) (old 7 f) (old 7 T) (old 7 c) (old 7 d) (old 7 R) (old 7 S) (old 7 K) (old 7 H) (old 7 L) (old 7 M) (old 7 Base) (old 7 I) (old 7 j) (old 7 p) (old 7 x) (old 7 Name) (old 7 Whole) (old 7 Img) (old 7 D) (old 7 Nraw) (old 7 Y) (old 7 R1) (old 7 S1) (old 7 K1) (old 7 H1) (old 7 L1) (old 7 M1) (old 7 q) (old 7 Y1)
    (fun i => old 3 (slot 4 i)) (slot 3) hf7 hg7 hr7 hy7 hy17

/-- Actual TWO openings and typed base, with NO pre-supplied canonical H
images. The following comparison produces those images internally. -/
def opening {m} (k : Nat) (w z a A B f T c d R S K H L M Base I j p x Name : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxMixedImageCodeSyntax.termLists w a f z T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A c K H).conj ((SyntaxCodedMixedBinderSyntax.lifted w K H A f c T B d L M).conj ((ForcingReflexiveImages.replacement w f d T Base j p S).conj ((SyntaxNumeralSyntax.numeral k I).conj ((SyntaxNumeralSyntax.numeral (k+1) j).conj ((SyntaxNumeralSyntax.numeral (k+2) f).conj ((SyntaxVariableSyntax.code true w z x).conj ((SyntaxMixedImageHead.head w d T z Name).conj (SyntaxMixedImageCodeSyntax.termList w f d T Base)))))))))))

theorem opening_rename {m l} (k : Nat) (w z a A B f T c d R S K H L M Base I j p x Name : Fin m) (ρ : Fin m → Fin l) :
    (opening k w z a A B f T c d R S K H L M Base I j p x Name).rename ρ = opening k (ρ w) (ρ z) (ρ a) (ρ A) (ρ B) (ρ f) (ρ T) (ρ c) (ρ d) (ρ R) (ρ S) (ρ K) (ρ H) (ρ L) (ρ M) (ρ Base) (ρ I) (ρ j) (ρ p) (ρ x) (ρ Name) := by
  simp only [opening, Formula.rename, omega_rename, empty_rename, SyntaxMixedImageCodeSyntax.termLists_rename,
    SyntaxCodedMixedBinderSyntax.lifted_rename, ForcingReflexiveImages.replacement_rename,
    SyntaxNumeralSyntax.numeral_rename, SyntaxVariableSyntax.code_rename, SyntaxMixedImageHead.head_rename, SyntaxMixedImageCodeSyntax.termList_rename]

private theorem frame_of_opening {k m} {Γ : Context m} (w z a A B f T c d R S K H L M Base I j p x Name Whole Img D : Fin m)
    (hf : Derives Γ (opening k w z a A B f T c d R S K H L M Base I j p x Name))
    (hi : Derives Γ (ForcingExistDomainImages.data k w f j d T Base I Name Whole Img D)) :
    Derives Γ (frame k w z a A B f T c d R S K H L M Base I j p x Name Whole Img D) :=
  Derives.conjI (Derives.conjL (hf)) (Derives.conjI (Derives.conjL (Derives.conjR (hf))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (hf)))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hf))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))))))) (Derives.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))))) (hi)))))))))))

/-- BOTH complete original domain compilers and ACTUAL double-opened outputs
are compared. Canonical THREE image witnesses and original FOUR compiler plus
THREE source-H witnesses are all generated/eliminated in the OBJECT theory. -/
theorem compare_prefixes {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Nraw Y R1 S1 K1 H1 L1 M1 q Nraw1 Y1 : Fin m)
    (hf : Derives Γ (opening k w z a A B f T c d R S K H L M Base I j p x Name))
    (hg : Derives Γ (opening k w z a A B f T c d R1 S1 K1 H1 L1 M1 Base I j q x Name))
    (hc : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M B f d T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 B f d T Nraw1 Y1)) : Derives Γ (.equal Y Y1) := by
  have hImagesInput : Derives Γ (ForcingExistDomainImages.input k w f j d T Base I Name) :=
    .conjI (Derives.conjL (hf)) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))))) (.conjI (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))))))
      (.conjI (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf)))))))))))) (.conjR (.conjR (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hf))))))))))))))))))
  let E := ForcingExistDomainImages.body k w f j d T Base I Name
  let Δ := Context.add E (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 E _ (ForcingExistDomainImages.produce hZ w f j d T Base I Name hImagesInput)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hf3 := of_eq (opening_rename k w z a A B f T c d R S K H L M Base I j p x Name (old 3)) (HornBinderRules.under_body 3 hf E)
  have hg3 := of_eq (opening_rename k w z a A B f T c d R1 S1 K1 H1 L1 M1 Base I j q x Name (old 3)) (HornBinderRules.under_body 3 hg E)
  have hFrame := frame_of_opening (old 3 w) (old 3 z) (old 3 a) (old 3 A) (old 3 B) (old 3 f) (old 3 T) (old 3 c) (old 3 d) (old 3 R) (old 3 S) (old 3 K) (old 3 H) (old 3 L) (old 3 M) (old 3 Base) (old 3 I) (old 3 j) (old 3 p) (old 3 x) (old 3 Name) (slot 3 0) (slot 3 1) (slot 3 2) hf3 hE
  have hFrame1 := frame_of_opening (old 3 w) (old 3 z) (old 3 a) (old 3 A) (old 3 B) (old 3 f) (old 3 T) (old 3 c) (old 3 d) (old 3 R1) (old 3 S1) (old 3 K1) (old 3 H1) (old 3 L1) (old 3 M1) (old 3 Base) (old 3 I) (old 3 j) (old 3 q) (old 3 x) (old 3 Name) (slot 3 0) (slot 3 1) (slot 3 2) hg3 hE
  have hc3 := of_eq (ForcingGuardCode.compiled_rename true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw (old 3)) (HornBinderRules.under_body 3 hc E)
  have hd3 := of_eq (ForcingGuardCode.compiled_rename true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw1 (old 3)) (HornBinderRules.under_body 3 hd E)
  have hy3 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L M B f d T Nraw Y (old 3)) (HornBinderRules.under_body 3 hy E)
  have hy13 := of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L1 M1 B f d T Nraw1 Y1 (old 3)) (HornBinderRules.under_body 3 hy1 E)
  exact compare_at_images (HornBinderRules.zf_body 3 hZ E) Dom (old 3 w) (old 3 z) (old 3 a) (old 3 A) (old 3 B) (old 3 f) (old 3 T) (old 3 c) (old 3 d) (old 3 R) (old 3 S) (old 3 K) (old 3 H) (old 3 L) (old 3 M) (old 3 Base) (old 3 I) (old 3 j) (old 3 p) (old 3 x) (old 3 Name) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 Nraw) (old 3 Y) (old 3 R1) (old 3 S1) (old 3 K1) (old 3 H1) (old 3 L1) (old 3 M1) (old 3 q) (old 3 Nraw1) (old 3 Y1) hFrame hFrame1 hc3 hd3 hy3 hy13

theorem compare {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (Dom : Source.Formula (k+1))
    (w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1 : Fin m)
    (hf : Derives Γ (opening k w z a A B f T c d R S K H L M Base I j p x Name))
    (hg : Derives Γ (opening k w z a A B f T c d R S1 K1 H1 L1 M1 Base I j q x Name))
    (hc : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw))
    (hd : Derives Γ (ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw1))
    (hy : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M B f d T Nraw Y))
    (hy1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 B f d T Nraw1 Y1)) : Derives Γ (.equal Y Y1) :=
  compare_prefixes hZ Dom w z a A B f T c d R S K H L M Base I j p x Name Nraw Y R S1 K1 H1 L1 M1 q Nraw1 Y1
    hf hg hc hd hy hy1

def input {k m} (Dom : Source.Formula (k+1)) (w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1 : Fin m) : Formula m :=
  (opening k w z a A B f T c d R S K H L M Base I j p x Name).conj ((opening k w z a A B f T c d R S1 K1 H1 L1 M1 Base I j q x Name).conj ((ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw).conj ((ForcingGuardCode.compiled true (ForcingExistGuardsCode.domainOrder Dom) w B f x Nraw1).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w L M B f d T Nraw Y).conj (SyntaxMixedFormulaJudgmentSyntax.substituted w L1 M1 B f d T Nraw1 Y1)))))

def sentence {k m} (Dom : Source.Formula (k+1)) (w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1 : Fin m) : Source.Sentence :=
  ((input Dom w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1).imp (.equal Y Y1)).close
theorem kernel_certificate {k m} (Dom : Source.Formula (k+1)) (w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1 : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence Dom w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let G := input Dom w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1
  let Γ := Context.add G (Source.SetLanguage.ZF.at m)
  have hG : Derives Γ G := .hyp (Or.inl rfl)
  exact compare (ZFContext.add (ZFContext.source_ZF m) G) Dom w z a A B f T c d R S K H L M Base I j p x Name Nraw Y S1 K1 H1 L1 M1 q Nraw1 Y1
    (Derives.conjL (hG))
    (Derives.conjL (Derives.conjR (hG)))
    (Derives.conjL (Derives.conjR (Derives.conjR (hG))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (hG)))))
    (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))
    (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (hG))))))

end PPAC.Migration.ForcingExistDomainOpening
