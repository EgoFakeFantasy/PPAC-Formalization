import PPAC.Migration.ForcingFreshBackground
import PPAC.Migration.ForcingNestedGuardProof

/-! Fresh opening of a one-bound-variable body: free weakening, actual
InstantiateTop at fresh free0, then actual AbstractTop. Reuse original
variable fields and the existing full four-path formula cancellation;
no second induction, evaluator, syntax checker or proof kernel. -/
namespace PPAC.Migration.ForcingFreshOpeningInverse
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxCodedMixedTermSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

def frame {m} (w z b A B t I J R S L M K H : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A z).conj
    ((SyntaxVariableSyntax.code false w z t).conj
      ((SyntaxIdentityMapSyntax.identityCode w A I).conj
        ((SyntaxFreeShiftSyntax.shiftCode w b B J).conj
          ((IndexTermImageCodeSyntax.environment w I J R S A b A B).conj
            ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z B A t L M).conj
              (SyntaxTopCodedEnvironmentSyntax.abstractCoded w z b A B K H))))))))
theorem frame_rename {m l} (w z b A B t I J R S L M K H : Fin m) (ρ : Fin m → Fin l) :
    (frame w z b A B t I J R S L M K H).rename ρ =
      frame (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ t) (ρ I) (ρ J) (ρ R) (ρ S) (ρ L) (ρ M) (ρ K) (ρ H) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxVariableSyntax.code_rename, SyntaxIdentityMapSyntax.identityCode_rename,
    SyntaxFreeShiftSyntax.shiftCode_rename, IndexTermImageCodeSyntax.environment_rename,
    SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename]

def path {m} (w z b A B R S L M K H x u v y : Fin m) : Formula m :=
  (substituted w R S A b A B x u).conj
    ((substituted w L M A B z B u v).conj (substituted w K H z B A b v y))
theorem path_rename {m l} (w z b A B R S L M K H x u v y : Fin m) (ρ : Fin m → Fin l) :
    (path w z b A B R S L M K H x u v y).rename ρ =
      path (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ R) (ρ S) (ρ L) (ρ M) (ρ K) (ρ H) (ρ x) (ρ u) (ρ v) (ρ y) := by
  simp only [path, Formula.rename, substituted_rename]

private structure Inputs {m} (Γ : Context m) (w z b A B t I J R S L M K H x u v y : Fin m) : Prop where
  zf : ZFContext.Evidence Γ
  hf : Derives Γ (frame w z b A B t I J R S L M K H)
  hp : Derives Γ (path w z b A B R S L M K H x u v y)
private theorem Inputs.in_body {m l} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) (E : Formula (m+l)) :
    Inputs (Context.add E (raisedContext l Γ)) (old l w) (old l z) (old l b) (old l A) (old l B) (old l t)
      (old l I) (old l J) (old l R) (old l S) (old l L) (old l M) (old l K) (old l H)
      (old l x) (old l u) (old l v) (old l y) :=
  ⟨HornBinderRules.zf_body l h.zf E,
    of_eq (frame_rename w z b A B t I J R S L M K H (old l)) (HornBinderRules.under_body l h.hf E),
    of_eq (path_rename w z b A B R S L M K H x u v y (old l)) (HornBinderRules.under_body l h.hp E)⟩

private theorem Inputs.hw {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (omega w) := .conjL h.hf
private theorem Inputs.hz {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (empty z) := .conjL (.conjR h.hf)
private theorem Inputs.hA {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (successor A z) := .conjL (.conjR (.conjR h.hf))
private theorem Inputs.fresh {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (SyntaxVariableSyntax.code false w z t) :=
  .conjL (.conjR (.conjR (.conjR h.hf)))
private theorem Inputs.identity {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (SyntaxIdentityMapSyntax.identityCode w A I) :=
  .conjL (.conjR (.conjR (.conjR (.conjR h.hf))))
private theorem Inputs.shift {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))
private theorem Inputs.weak {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S A b A B) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.hf))))))
private theorem Inputs.inst {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z B A t L M) :=
  .conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))))
private theorem Inputs.abs {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w z b A B K H) :=
  .conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR h.hf)))))))

private theorem value_subst {m} {Γ : Context m} (bound : Bool) (w i x y : Fin m)
    (he : Derives Γ (.equal x y)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w i x)) :
    Derives Γ (SyntaxVariableSyntax.code bound w i y) := by
  let P := SyntaxVariableSyntax.code bound w.castSucc i.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))
private theorem index_subst {m} {Γ : Context m} (bound : Bool) (w i j x : Fin m)
    (he : Derives Γ (.equal i j)) (hc : Derives Γ (SyntaxVariableSyntax.code bound w i x)) :
    Derives Γ (SyntaxVariableSyntax.code bound w j x) := by
  let P := SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) x.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, SyntaxVariableSyntax.code_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))

private theorem bound_zero {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y)
    (hx : Derives Γ (SyntaxVariableSyntax.code true w z x)) : Derives Γ (.equal x y) := by
  let E := (SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) A.castSucc A.castSucc I.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last m))
  apply Derives.exE (p := E) h.identity
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have h1 := h.in_body E
  have hx1 := of_eq (SyntaxVariableSyntax.code_rename true w z x Fin.castSucc) (SourceLogic.under hx E)
  have f0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h1.zf true
    w.castSucc R.castSucc S.castSucc A.castSucc b.castSucc A.castSucc B.castSucc x.castSucc u.castSucc z.castSucc
    h1.hw (IndexTermImageCodeTyping.environment_lists _ _ _ _ _ _ _ _ _ h1.weak) hx1)) (.conjL h1.hp)
  have edge := SyntaxIdentityUnique.diagonal_edge w.castSucc A.castSucc (Fin.last m) z.castSucc
    (.conjR (.conjL hE)) (.conjR hE) (.conjL f0)
  have hu := Derives.impE (.conjL (IndexTermImageCodeFields.at_edge h1.zf true
    w.castSucc I.castSucc R.castSucc A.castSucc A.castSucc B.castSucc (Fin.last m) z.castSucc z.castSucc u.castSucc
    (.conjL h1.weak) (.conjL hE) edge)) f0
  have f1 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h1.zf true
    w.castSucc L.castSucc M.castSucc A.castSucc B.castSucc z.castSucc B.castSucc u.castSucc v.castSucc z.castSucc
    h1.hw (SyntaxTopCodedEnvironmentTyping.instantiate_lists _ _ _ _ _ _ _ h1.inst) hu)) (.conjL (.conjR h1.hp))
  have ev := Derives.impE (.conjL (SyntaxTopCodedEnvironmentFields.instantiate_zero h1.zf
    w.castSucc z.castSucc B.castSucc A.castSucc t.castSucc L.castSucc M.castSucc z.castSucc v.castSucc h1.hw h1.inst h1.hz)) f1
  have hv := value_subst false w.castSucc z.castSucc t.castSucc v.castSucc (eq_symm ev) h1.fresh
  have f2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h1.zf false
    w.castSucc K.castSucc H.castSucc z.castSucc B.castSucc A.castSucc b.castSucc v.castSucc y.castSucc z.castSucc
    h1.hw (SyntaxTopCodedEnvironmentTyping.abstract_lists _ _ _ _ _ _ _ h1.abs) hv)) (.conjR (.conjR h1.hp))
  have hy := Derives.impE (.conjL (SyntaxTopCodedEnvironmentFields.abstract_zero h1.zf
    w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc K.castSucc H.castSucc z.castSucc y.castSucc h1.hw h1.abs h1.hz)) f2
  exact SyntaxVariables.unique h1.zf true w.castSucc z.castSucc x.castSucc y.castSucc h1.hw hx1 hy

private theorem bound_index {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) (i : Fin m)
    (hi : Derives Γ (.mem i A)) (hx : Derives Γ (SyntaxVariableSyntax.code true w i x)) :
    Derives Γ (.equal x y) := by
  have cases := InsertLogic.member_cases A z z i h.hA hi
  apply Derives.disjE cases
  · exact .botE (.impE (empty_at z i (add h.hz _)) (.hyp (Or.inl rfl)))
  · have iz : Derives (Context.add (.equal i z) Γ) (.equal i z) := .hyp (Or.inl rfl)
    exact bound_zero ⟨ZFContext.add h.zf _,add h.hf _,add h.hp _⟩
      (index_subst true w i z x iz (add hx _))

private theorem free_index {m} {Γ : Context m} {w z b A B t I J R S L M K H x u v y : Fin m}
    (h : Inputs Γ w z b A B t I J R S L M K H x u v y) (i : Fin m)
    (hi : Derives Γ (.mem i b)) (hx : Derives Γ (SyntaxVariableSyntax.code false w i x)) :
    Derives Γ (.equal x y) := by
  -- Reuse the original FreshBackground free-variable field argument, now
  -- at bound scope A and with the ACTUAL middle InstantiateTop query.
  let E0 := (SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) b.castSucc B.castSucc J.castSucc).conj
    (SyntaxFreeShiftSyntax.shiftMap w.castSucc b.castSucc B.castSucc (Fin.last m))
  let Δ1 := Context.add E0 (Context.image Formula.raise Γ)
  apply Derives.exE (p := E0) h.shift
  have hE0 : Derives Δ1 E0 := .hyp (Or.inl rfl)
  have h1 := h.in_body E0
  let E1 := successor (Fin.last (m+1)) i.castSucc.castSucc
  let Δ2 := Context.add E1 (Context.image Formula.raise Δ1)
  apply Derives.exE (p := E1) (InsertExistence.exists_insert i.castSucc i.castSucc
    (ZFContext.arithmetic h1.zf).base.pairing (ZFContext.arithmetic h1.zf).base.union)
  have hE1 : Derives Δ2 E1 := .hyp (Or.inl rfl)
  have h2 := h1.in_body E1
  have hi2 : Derives Δ2 (.mem i.castSucc.castSucc b.castSucc.castSucc) := SourceLogic.under (SourceLogic.under hi E0) E1
  have hx2 : Derives Δ2 (SyntaxVariableSyntax.code false w.castSucc.castSucc i.castSucc.castSucc x.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, SyntaxVariableSyntax.code_rename])
    (SourceLogic.under (SourceLogic.under hx E0) E1)
  have hg : Derives Δ2 ((SyntaxMapCodeSyntax.encoded w.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc B.castSucc.castSucc J.castSucc.castSucc).conj
    (SyntaxFreeShiftSyntax.shiftMap w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc)) :=
    of_eq (by simp only [E0, Formula.raise, Formula.rename, SyntaxMapCodeSyntax.encoded_rename,
      SyntaxFreeShiftSyntax.shiftMap_rename]) (SourceLogic.under hE0 E1)
  have edge := Derives.impE (.conjR (SyntaxFreeShiftGraph.edge_iff b.castSucc.castSucc (Fin.last m).castSucc
    i.castSucc.castSucc (Fin.last (m+1)) (SyntaxFreeShiftGraph.to_graph _ _ _ _ (.conjR hg)))) (.conjI hi2 hE1)
  have hj := SyntaxIndexMapSyntax.edge_target w.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc B.castSucc.castSucc
    i.castSucc.castSucc (Fin.last (m+1)) (.conjL (.conjR (.conjR hg))) edge
  have f0 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h2.zf false
    w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc
    x.castSucc.castSucc u.castSucc.castSucc i.castSucc.castSucc h2.hw
    (IndexTermImageCodeTyping.environment_lists _ _ _ _ _ _ _ _ _ h2.weak) hx2)) (.conjL h2.hp)
  have hu := Derives.impE (.conjL (IndexTermImageCodeFields.at_edge h2.zf false
    w.castSucc.castSucc J.castSucc.castSucc S.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc
    (Fin.last m).castSucc i.castSucc.castSucc (Fin.last (m+1)) u.castSucc.castSucc
    (.conjR h2.weak) (.conjL hg) edge)) f0
  have f1 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h2.zf false
    w.castSucc.castSucc L.castSucc.castSucc M.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc B.castSucc.castSucc
    u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1)) h2.hw
    (SyntaxTopCodedEnvironmentTyping.instantiate_lists _ _ _ _ _ _ _ h2.inst) hu)) (.conjL (.conjR h2.hp))
  have hv := Derives.impE (.conjL (SyntaxTopCodedEnvironmentFields.instantiate_free h2.zf
    w.castSucc.castSucc z.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc
    L.castSucc.castSucc M.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc h2.inst hj)) f1
  have f2 := Derives.impE (.conjL (SyntaxCodedMixedTermFields.at_field h2.zf false
    w.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc z.castSucc.castSucc B.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc
    v.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1)) h2.hw
    (SyntaxTopCodedEnvironmentTyping.abstract_lists _ _ _ _ _ _ _ h2.abs) hv)) (.conjR (.conjR h2.hp))
  have hy := Derives.impE (.conjL (SyntaxTopCodedEnvironmentFields.abstract_free h2.zf
    w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc
    K.castSucc.castSucc H.castSucc.castSucc (Fin.last (m+1)) i.castSucc.castSucc y.castSucc.castSucc h2.hw h2.abs hi2 hE1)) f2
  exact SyntaxVariables.unique h2.zf false w.castSucc.castSucc i.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc h2.hw hx2 hy

/-- All internal terms in the original singleton-bound source scope.
The fresh bound0 and arbitrary (possibly nonstandard) free indices are
handled by original object scope elimination and actual operation fields. -/
theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t I J R S L M K H x u v y : Fin m)
    (hf : Derives Γ (frame w z b A B t I J R S L M K H))
    (hp : Derives Γ (path w z b A B R S L M K H x u v y)) : Derives Γ (.equal x y) := by
  have h : Inputs Γ w z b A B t I J R S L M K H x u v y := ⟨hZ,hf,hp⟩
  apply OriginalTermScopeElimination.eliminate w A b x (.equal x y)
    (SyntaxCodedMixedTermTyping.source_type w R S A b A B x u (.conjL hp))
  intro bound
  cases bound
  · let E := SyntaxTermSyntax.branchWitness false w b x
    have hE : Derives (Context.add E (Context.image Formula.raise Γ)) E := .hyp (Or.inl rfl)
    exact free_index (h.in_body E) (Fin.last m) (.conjL hE) (.conjR hE)
  · let E := SyntaxTermSyntax.branchWitness true w A x
    have hE : Derives (Context.add E (Context.image Formula.raise Γ)) E := .hyp (Or.inl rfl)
    exact bound_index (h.in_body E) (Fin.last m) (.conjL hE) (.conjR hE)

private def four {α : Type} (a b c d : α) : Fin 4 → α :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

/-- All FIVE term candidates are quantified internally; the direct identity
uses the SAME bound identity code as the original weakening. -/
theorem term_diagram {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t I J R S L M K H J3 R3 S3 : Fin m)
    (hf : Derives Γ (frame w z b A B t I J R S L M K H))
    (hj : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b J3))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J3 R3 S3 A b A b)) :
    Derives Γ (ForcingTermDiagram.diagram w (four A A z A) (four b B B b)
      (four R L K R3) (four S M H S3)) := by
  apply OriginalUniversalBlock.intro_many 5
  apply Derives.impI
  let P := (ForcingTermDiagram.step (old 5 w) (four (old 5 A) (old 5 A) (old 5 z) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 B) (old 5 b)) (four (old 5 R) (old 5 L) (old 5 K) (old 5 R3))
      (four (old 5 S) (old 5 M) (old 5 H) (old 5 S3)) 0 (slot 5 0) (slot 5 1)).conj
    ((ForcingTermDiagram.step (old 5 w) (four (old 5 A) (old 5 A) (old 5 z) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 B) (old 5 b)) (four (old 5 R) (old 5 L) (old 5 K) (old 5 R3))
      (four (old 5 S) (old 5 M) (old 5 H) (old 5 S3)) 1 (slot 5 1) (slot 5 2)).conj
      ((ForcingTermDiagram.step (old 5 w) (four (old 5 A) (old 5 A) (old 5 z) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 B) (old 5 b)) (four (old 5 R) (old 5 L) (old 5 K) (old 5 R3))
      (four (old 5 S) (old 5 M) (old 5 H) (old 5 S3)) 2 (slot 5 2) (slot 5 3)).conj
        (ForcingTermDiagram.step (old 5 w) (four (old 5 A) (old 5 A) (old 5 z) (old 5 A))
      (four (old 5 b) (old 5 B) (old 5 B) (old 5 b)) (four (old 5 R) (old 5 L) (old 5 K) (old 5 R3))
      (four (old 5 S) (old 5 M) (old 5 H) (old 5 S3)) 3 (slot 5 0) (slot 5 4))))
  let Δ := Context.add P (raisedContext 5 Γ)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hf5 := of_eq (frame_rename w z b A B t I J R S L M K H (old 5)) (HornBinderRules.under_body 5 hf P)
  have hZ5 := HornBinderRules.zf_body 5 hZ P
  have h0 : Derives Δ (path (old 5 w) (old 5 z) (old 5 b) (old 5 A) (old 5 B)
    (old 5 R) (old 5 S) (old 5 L) (old 5 M) (old 5 K) (old 5 H)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3)) :=
    .conjI (.conjL hP) (.conjI (.conjL (.conjR hP)) (.conjL (.conjR (.conjR hP))))
  have eq0 := term hZ5 (old 5 w) (old 5 z) (old 5 b) (old 5 A) (old 5 B) (old 5 t)
    (old 5 I) (old 5 J) (old 5 R) (old 5 S) (old 5 L) (old 5 M) (old 5 K) (old 5 H)
    (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) hf5 h0
  have id0 := ForcingBinderFormula.identity_term_output hZ5 (old 5 w) (old 5 A) (old 5 b)
    (old 5 I) (old 5 J3) (old 5 R3) (old 5 S3) (slot 5 0) (slot 5 4)
    (.conjL hf5) (.conjL (.conjR (.conjR (.conjR (.conjR hf5)))))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w b J3 (old 5)) (HornBinderRules.under_body 5 hj P))
    (of_eq (IndexTermImageCodeSyntax.environment_rename w I J3 R3 S3 A b A b (old 5)) (HornBinderRules.under_body 5 he P))
    (.conjR (.conjR (.conjR hP)))
  exact eq_trans (eq_symm eq0) id0

private theorem at_tables {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t I J R S L M K H F U V Q J3 R3 S3 : Fin m)
    (hf : Derives Γ (frame w z b A B t I J R S L M K H))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b A B F U))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M A B z B U V))
    (h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H z B A b V Q))
    (hj : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b J3))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J3 R3 S3 A b A b)) :
    Derives Γ (.equal Q F) := by
  have hw := Derives.conjL hf
  have hI := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have hF := Derives.conjL (SyntaxMixedFormulaOutput.input_of_substituted hZ w R S A b A B F U hw h0)
  have hs := ForcingScopeIdentity.reflexive hZ w I J3 A b A b F hw hI hj hF
  have h3 := IndexFormulaRenameInduction.forward hZ w I J3 R3 S3 A b A b F F hw he hs
  exact ForcingFormulaInduction.cancel hZ w (four A A z A) (four b B B b) (four R L K R3) (four S M H S3)
    F U V Q F hw (term_diagram hZ w z b A B t I J R S L M K H J3 R3 S3 hf hj he) h0 h1 h2 h3

private theorem after_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t I J R S L M K H F U V Q J3 : Fin m)
    (hf : Derives Γ (frame w z b A B t I J R S L M K H))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b A B F U))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M A B z B U V))
    (h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H z B A b V Q))
    (hj : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b J3)) :
    Derives Γ (.equal Q F) := by
  have hI := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have he := IndexTermImageEnvironment.exists_environment hZ w I J3 A b A b (.conjL hf)
    (SyntaxIdentityCode.map_code w A I hI) (SyntaxIdentityCode.map_code w b J3 hj)
  let E := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 I) (old 2 J3) (slot 2 0) (slot 2 1)
    (old 2 A) (old 2 b) (old 2 A) (old 2 b)
  apply HornBinderRules.eliminate_many 2 E _ he
  exact at_tables (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 z) (old 2 b) (old 2 A) (old 2 B) (old 2 t)
    (old 2 I) (old 2 J) (old 2 R) (old 2 S) (old 2 L) (old 2 M) (old 2 K) (old 2 H)
    (old 2 F) (old 2 U) (old 2 V) (old 2 Q) (old 2 J3) (slot 2 0) (slot 2 1)
    (of_eq (frame_rename w z b A B t I J R S L M K H (old 2)) (HornBinderRules.under_body 2 hf E))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S A b A B F U (old 2)) (HornBinderRules.under_body 2 h0 E))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L M A B z B U V (old 2)) (HornBinderRules.under_body 2 h1 E))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H z B A b V Q (old 2)) (HornBinderRules.under_body 2 h2 E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w b J3 (old 2)) (HornBinderRules.under_body 2 hj E))
    (.hyp (Or.inl rfl))

/-- All internally coded formulas, including nonstandard codes and binders.
The direct identity code and BOTH converted tables are generated/eliminated;
the original complete formula cancellation is ACTUALLY called. -/
theorem formula {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t I J R S L M K H F U V Q : Fin m)
    (hf : Derives Γ (frame w z b A B t I J R S L M K H))
    (h0 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b A B F U))
    (h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L M A B z B U V))
    (h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H z B A b V Q)) :
    Derives Γ (.equal Q F) := by
  have hw := Derives.conjL hf
  have hF := Derives.conjL (SyntaxMixedFormulaOutput.input_of_substituted hZ w R S A b A B F U hw h0)
  have hb := Derives.conjR (.conjR (FormulaCodeProperties.guards w F A b hF))
  let E := SyntaxIdentityMapSyntax.identityCode w.castSucc b.castSucc (Fin.last m)
  apply Derives.exE (p := E) (SyntaxIdentityCode.exists_code hZ w b hw hb)
  exact after_identity (ZFContext.under hZ E) w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc t.castSucc
    I.castSucc J.castSucc R.castSucc S.castSucc L.castSucc M.castSucc K.castSucc H.castSucc
    F.castSucc U.castSucc V.castSucc Q.castSucc (Fin.last m)
    (of_eq (frame_rename w z b A B t I J R S L M K H Fin.castSucc) (SourceLogic.under hf E))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w R S A b A B F U Fin.castSucc) (SourceLogic.under h0 E))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w L M A B z B U V Fin.castSucc) (SourceLogic.under h1 E))
    (of_eq (SyntaxMixedFormulaJudgmentSyntax.substituted_rename w K H z B A b V Q Fin.castSucc) (SourceLogic.under h2 E))
    (.hyp (Or.inl rfl))

def sentence {m} (w z b A B t I J R S L M K H F U V Q : Fin m) : Source.Sentence :=
  (((frame w z b A B t I J R S L M K H).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b A B F U).conj
      ((SyntaxMixedFormulaJudgmentSyntax.substituted w L M A B z B U V).conj
        (SyntaxMixedFormulaJudgmentSyntax.substituted w K H z B A b V Q)))).imp (.equal Q F)).close
theorem kernel_certificate {m} (w z b A B t I J R S L M K H F U V Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z b A B t I J R S L M K H F U V Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact formula (ZFContext.add (ZFContext.source_ZF m) _) w z b A B t I J R S L M K H F U V Q
    (.conjL (.hyp (Or.inl rfl))) (.conjL (.conjR (.hyp (Or.inl rfl))))
    (.conjL (.conjR (.conjR (.hyp (Or.inl rfl))))) (.conjR (.conjR (.conjR (.hyp (Or.inl rfl)))))

def operationInput {m} (w z b A B t F U V Q : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A z).conj
    ((SyntaxVariableSyntax.code false w z t).conj
      ((SyntaxWeakenFreeSyntax.weakened w A b B F U).conj
        ((SyntaxTopFormulaSyntax.instantiated w z B A t U V).conj
          (SyntaxTopFormulaSyntax.abstracted w z b A B V Q))))))
theorem operationInput_rename {m l} (w z b A B t F U V Q : Fin m) (ρ : Fin m → Fin l) :
    (operationInput w z b A B t F U V Q).rename ρ =
      operationInput (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ t) (ρ F) (ρ U) (ρ V) (ρ Q) := by
  simp only [operationInput, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxVariableSyntax.code_rename, SyntaxWeakenFreeSyntax.weakened_rename,
    SyntaxTopFormulaSyntax.instantiated_rename, SyntaxTopFormulaSyntax.abstracted_rename]

private structure OpParams (m : Nat) where
  w : Fin m
  z : Fin m
  b : Fin m
  A : Fin m
  B : Fin m
  t : Fin m
  F : Fin m
  U : Fin m
  V : Fin m
  Q : Fin m
private def OpParams.map {m l} (p : OpParams m) (ρ : Fin m → Fin l) : OpParams l :=
  ⟨ρ p.w,ρ p.z,ρ p.b,ρ p.A,ρ p.B,ρ p.t,ρ p.F,ρ p.U,ρ p.V,ρ p.Q⟩
private def weakState {m} (p : OpParams m) (I J : Fin m) : Formula m :=
  (SyntaxIdentityMapSyntax.identityCode p.w p.A I).conj
    ((SyntaxFreeShiftSyntax.shiftCode p.w p.b p.B J).conj
      (SyntaxRenameJudgmentSyntax.renamed p.w I J p.A p.b p.A p.B p.F p.U))
private theorem weakState_rename {m l} (p : OpParams m) (I J : Fin m) (ρ : Fin m → Fin l) :
    (weakState p I J).rename ρ = weakState (p.map ρ) (ρ I) (ρ J) := by
  simp only [weakState, OpParams.map, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename,
    SyntaxFreeShiftSyntax.shiftCode_rename, SyntaxRenameJudgmentSyntax.renamed_rename]

private theorem at_operations {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (p : OpParams m)
    (I J L M K H : Fin m)
    (hi : Derives Γ (operationInput p.w p.z p.b p.A p.B p.t p.F p.U p.V p.Q))
    (hwk : Derives Γ (weakState p I J))
    (hin : Derives Γ (SyntaxTopFormulaSyntax.instantiateState p.w p.z p.B p.A p.t p.U p.V L M))
    (hab : Derives Γ (SyntaxTopFormulaSyntax.abstractState p.w p.z p.b p.A p.B p.V p.Q K H)) :
    Derives Γ (.equal p.Q p.F) := by
  have hw := Derives.conjL hi
  have he := IndexTermImageEnvironment.exists_environment hZ p.w I J p.A p.b p.A p.B hw
    (SyntaxIdentityCode.map_code p.w p.A I (.conjL hwk))
    (SyntaxFreeShiftCode.map_code p.w p.b p.B J (.conjL (.conjR hwk)))
  let E := IndexTermImageCodeSyntax.environment (old 2 p.w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 p.A) (old 2 p.b) (old 2 p.A) (old 2 p.B)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _ he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ E
  have hi2 := of_eq (operationInput_rename p.w p.z p.b p.A p.B p.t p.F p.U p.V p.Q (old 2)) (HornBinderRules.under_body 2 hi E)
  have hwk2 := of_eq (weakState_rename p I J (old 2)) (HornBinderRules.under_body 2 hwk E)
  have hin2 := of_eq (SyntaxTopFormulaSyntax.instantiateState_rename p.w p.z p.B p.A p.t p.U p.V L M (old 2))
    (HornBinderRules.under_body 2 hin E)
  have hab2 := of_eq (SyntaxTopFormulaSyntax.abstractState_rename p.w p.z p.b p.A p.B p.V p.Q K H (old 2))
    (HornBinderRules.under_body 2 hab E)
  have hf : Derives Δ (frame (old 2 p.w) (old 2 p.z) (old 2 p.b) (old 2 p.A) (old 2 p.B) (old 2 p.t)
    (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (old 2 L) (old 2 M) (old 2 K) (old 2 H)) :=
    .conjI (.conjL hi2) (.conjI (.conjL (.conjR hi2)) (.conjI (.conjL (.conjR (.conjR hi2)))
      (.conjI (.conjL (.conjR (.conjR (.conjR hi2)))) (.conjI (.conjL hwk2)
        (.conjI (.conjL (.conjR hwk2)) (.conjI hE (.conjI (.conjL hin2) (.conjL hab2))))))))
  have h0 := IndexFormulaRenameInduction.forward hZ2 (old 2 p.w) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (old 2 p.A) (old 2 p.b) (old 2 p.A) (old 2 p.B) (old 2 p.F) (old 2 p.U) (.conjL hi2) hE (.conjR (.conjR hwk2))
  exact formula hZ2 (old 2 p.w) (old 2 p.z) (old 2 p.b) (old 2 p.A) (old 2 p.B) (old 2 p.t)
    (old 2 I) (old 2 J) (slot 2 0) (slot 2 1) (old 2 L) (old 2 M) (old 2 K) (old 2 H)
    (old 2 p.F) (old 2 p.U) (old 2 p.V) (old 2 p.Q) hf h0 (.conjR hin2) (.conjR hab2)

private theorem after_instantiated {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (p : OpParams m)
    (I J L M : Fin m)
    (hi : Derives Γ (operationInput p.w p.z p.b p.A p.B p.t p.F p.U p.V p.Q))
    (hwk : Derives Γ (weakState p I J))
    (hin : Derives Γ (SyntaxTopFormulaSyntax.instantiateState p.w p.z p.B p.A p.t p.U p.V L M)) :
    Derives Γ (.equal p.Q p.F) := by
  have ha := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))
  let E := SyntaxTopFormulaSyntax.abstractBody p.w p.z p.b p.A p.B p.V p.Q
  apply HornBinderRules.eliminate_many 2 E _ ha
  exact at_operations (HornBinderRules.zf_body 2 hZ E) (p.map (old 2))
    (old 2 I) (old 2 J) (old 2 L) (old 2 M) (slot 2 0) (slot 2 1)
    (of_eq (operationInput_rename p.w p.z p.b p.A p.B p.t p.F p.U p.V p.Q (old 2)) (HornBinderRules.under_body 2 hi E))
    (of_eq (weakState_rename p I J (old 2)) (HornBinderRules.under_body 2 hwk E))
    (of_eq (SyntaxTopFormulaSyntax.instantiateState_rename p.w p.z p.B p.A p.t p.U p.V L M (old 2))
      (HornBinderRules.under_body 2 hin E)) (.hyp (Or.inl rfl))

private theorem after_weakened {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (p : OpParams m)
    (I J : Fin m)
    (hi : Derives Γ (operationInput p.w p.z p.b p.A p.B p.t p.F p.U p.V p.Q))
    (hwk : Derives Γ (weakState p I J)) : Derives Γ (.equal p.Q p.F) := by
  have hn := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi)))))
  let E := SyntaxTopFormulaSyntax.instantiateBody p.w p.z p.B p.A p.t p.U p.V
  apply HornBinderRules.eliminate_many 2 E _ hn
  exact after_instantiated (HornBinderRules.zf_body 2 hZ E) (p.map (old 2)) (old 2 I) (old 2 J) (slot 2 0) (slot 2 1)
    (of_eq (operationInput_rename p.w p.z p.b p.A p.B p.t p.F p.U p.V p.Q (old 2)) (HornBinderRules.under_body 2 hi E))
    (of_eq (weakState_rename p I J (old 2)) (HornBinderRules.under_body 2 hwk E)) (.hyp (Or.inl rfl))

/-- Consume the THREE actual original operations directly. All EIGHT
weakening/native-operation/environment witnesses and the THREE direct
identity witnesses are internally eliminated. No supplied maps or expected
code equality, and no external-standardness restriction. -/
theorem from_operations {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z b A B t F U V Q : Fin m)
    (hi : Derives Γ (operationInput w z b A B t F U V Q)) : Derives Γ (.equal Q F) := by
  have hw := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))
  let E := SyntaxWeakenFreeSyntax.body w A b B F U
  apply HornBinderRules.eliminate_many 2 E _ hw
  exact after_weakened (HornBinderRules.zf_body 2 hZ E)
    ⟨old 2 w,old 2 z,old 2 b,old 2 A,old 2 B,old 2 t,old 2 F,old 2 U,old 2 V,old 2 Q⟩ (slot 2 0) (slot 2 1)
    (of_eq (operationInput_rename w z b A B t F U V Q (old 2)) (HornBinderRules.under_body 2 hi E)) (.hyp (Or.inl rfl))

def operationSentence {m} (w z b A B t F U V Q : Fin m) : Source.Sentence :=
  ((operationInput w z b A B t F U V Q).imp (.equal Q F)).close
theorem operation_kernel_certificate {m} (w z b A B t F U V Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (operationSentence w z b A B t F U V Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_operations (ZFContext.add (ZFContext.source_ZF m) _) w z b A B t F U V Q (.hyp (Or.inl rfl))

def input {m} (w z b A B t F U V : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((successor A z).conj
    ((SyntaxVariableSyntax.code false w z t).conj
      ((SyntaxWeakenFreeSyntax.weakened w A b B F U).conj
        (SyntaxTopFormulaSyntax.instantiated w z B A t U V)))))
theorem input_rename {m l} (w z b A B t F U V : Fin m) (ρ : Fin m → Fin l) :
    (input w z b A B t F U V).rename ρ =
      input (ρ w) (ρ z) (ρ b) (ρ A) (ρ B) (ρ t) (ρ F) (ρ U) (ρ V) := by
  simp only [input, Formula.rename, omega_rename, empty_rename, successor_rename,
    SyntaxVariableSyntax.code_rename, SyntaxWeakenFreeSyntax.weakened_rename,
    SyntaxTopFormulaSyntax.instantiated_rename]
private theorem with_abstract {m} {Γ : Context m} (w z b A B t F U V Q : Fin m)
    (hi : Derives Γ (input w z b A B t F U V))
    (ha : Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B V Q)) :
    Derives Γ (operationInput w z b A B t F U V Q) :=
  .conjI (.conjL hi) (.conjI (.conjL (.conjR hi)) (.conjI (.conjL (.conjR (.conjR hi)))
    (.conjI (.conjL (.conjR (.conjR (.conjR hi)))) (.conjI (.conjL (.conjR (.conjR (.conjR (.conjR hi)))))
      (.conjI (.conjR (.conjR (.conjR (.conjR (.conjR hi))))) ha)))))

/-- Actual weakening and fresh instantiation suffice: produce the mode3
output internally and prove it is the SAME original body. No abstract
operation/output/equality is an input to this theorem. -/
theorem derive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z b A B t F U V : Fin m)
    (hi : Derives Γ (input w z b A B t F U V)) :
    Derives Γ (SyntaxTopFormulaSyntax.abstracted w z b A B V F) := by
  have hw := Derives.conjL hi
  have ha := Derives.conjL (Derives.conjR (Derives.conjR hi))
  have weak := Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))
  have inst := Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hi))))
  have weakInput := SyntaxWeakenFreeOutput.input_of_weakened hZ w A b B F U hw weak
  have instEnv := SyntaxTopFormulaTyping.instantiate_environment w z B A t U V inst
  have hzN := Derives.conjL (Derives.conjL (Derives.conjL instEnv))
  have hbN := Derives.conjR (Derives.conjR (FormulaCodeProperties.guards w F A b (.conjL weakInput)))
  have hEnv : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w z b A B) :=
    .conjI (.conjI hzN hbN) (.conjI ha (.conjR weakInput))
  have ht := SyntaxTopFormulaTyping.instantiate_target_type w z B A t U V inst
  have he := SyntaxTopFormulaExistence.abstract_exists hZ w z b A B V hw (.conjI hEnv ht)
  let E := SyntaxTopFormulaSyntax.abstracted w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc V.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) he
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hi1 := of_eq (input_rename w z b A B t F U V Fin.castSucc) (SourceLogic.under hi E)
  have eq := from_operations (ZFContext.under hZ E) w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc t.castSucc
    F.castSucc U.castSucc V.castSucc (Fin.last m)
    (with_abstract w.castSucc z.castSucc b.castSucc A.castSucc B.castSucc t.castSucc F.castSucc U.castSucc V.castSucc (Fin.last m) hi1 hE)
  let P := SyntaxTopFormulaSyntax.abstracted w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc
    A.castSucc.castSucc B.castSucc.castSucc V.castSucc.castSucc (Fin.last (m+1))
  exact of_eq (by simp only [P, Formula.raise, Formula.instantiate, SyntaxTopFormulaSyntax.abstracted_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P eq (of_eq (by simp only [P, Formula.instantiate, SyntaxTopFormulaSyntax.abstracted_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl) hE))

def deriveSentence {m} (w z b A B t F U V : Fin m) : Source.Sentence :=
  ((input w z b A B t F U V).imp (SyntaxTopFormulaSyntax.abstracted w z b A B V F)).close
theorem derive_kernel_certificate {m} (w z b A B t F U V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (deriveSentence w z b A B t F U V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact derive (ZFContext.add (ZFContext.source_ZF m) _) w z b A B t F U V (.hyp (Or.inl rfl))

/-- Actual consumer of the accepted literal nested-body production.
The actual original fresh INSTANCE into its K is computational input;
the generated mode3 answer is identified with the actual parent body. -/
theorem identify_nested {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B t F U G W M O Tail I K J : Fin m)
    (hi : Derives Γ (input w z b A B t F U K))
    (hd : Derives Γ (ForcingNestedGuardProof.data test w z b A B G W M O Tail I K J)) :
    Derives Γ (.equal J F) :=
  from_operations hZ w z b A B t F U K J
    (with_abstract w z b A B t F U K J hi (.conjL (.conjR (.conjR hd))))

private theorem single_body_subst {m} {Γ : Context m} (w F J P : Fin m)
    (he : Derives Γ (.equal F J)) (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F P)) :
    Derives Γ (SyntaxLogicalSyntax.singleCode 9 w J P) := by
  let X := SyntaxLogicalSyntax.singleCode 9 w.castSucc (Fin.last m) P.castSucc
  exact of_eq (by simp only [X, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst X he (of_eq (by simp only [X, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc))

/-- Match the actual parent ALL constructor and transport the ORIGINAL
generated conditional Root proof to that SAME parent code. This requires
the actual native instance-to-K record, not an assumed code equality.
Producing that record from the complete raw new-parent query remains the
source modal consumer's obligation. -/
theorem consume_nested {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w z b A B t F U G W M O Tail I K J Parent : Fin m)
    (hi : Derives Γ (input w z b A B t F U K))
    (hd : Derives Γ (ForcingNestedGuardProof.data test w z b A B G W M O Tail I K J))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode 9 w F Parent)) :
    Derives Γ (InternalProofBackground.implication test w z b G Parent) := by
  have he := identify_nested hZ test w z b A B t F U G W M O Tail I K J hi hd
  have hJ := single_body_subst w F J Parent (eq_symm he) hc
  have hp := Derives.conjR (Derives.conjR (Derives.conjR hd))
  let E := (SyntaxLogicalSyntax.singleCode 9 w.castSucc J.castSucc (Fin.last m)).conj
    (InternalProofBackground.implication test w.castSucc z.castSucc b.castSucc G.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hp
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have eq := SyntaxLogicalFields.single_unique (ZFContext.under hZ E) 9 w.castSucc J.castSucc (Fin.last m) Parent.castSucc
    (of_eq (omega_rename w Fin.castSucc) (SourceLogic.under (.conjL hi) E)) (.conjL hE)
    (of_eq (SyntaxLogicalSyntax.singleCode_rename 9 w J Parent Fin.castSucc) (SourceLogic.under hJ E))
  let P := InternalProofBackground.implication test w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc G.castSucc.castSucc (Fin.last (m+1))
  exact of_eq (by simp only [P, Formula.raise, Formula.instantiate, InternalProofBackground.implication_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P eq (of_eq (by simp only [P, Formula.instantiate, InternalProofBackground.implication_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjR hE)))

def consumeSentence {m} (target : Bool) (w z b A B t F U G W M O Tail I K J Parent : Fin m) : Source.Sentence :=
  (((input w z b A B t F U K).conj
    ((ForcingNestedGuardProof.data (OriginalAxiomCodeTest.test target) w z b A B G W M O Tail I K J).conj
      (SyntaxLogicalSyntax.singleCode 9 w F Parent))).imp
        (InternalProofBackground.implication (OriginalAxiomCodeTest.test target) w z b G Parent)).close
theorem consume_kernel_certificate {m} (target : Bool) (w z b A B t F U G W M O Tail I K J Parent : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
      (Translation.sentence (consumeSentence target w z b A B t F U G W M O Tail I K J Parent)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact consume_nested (ZFContext.add (ZFContext.source_ZF m) _) (OriginalAxiomCodeTest.test target)
    w z b A B t F U G W M O Tail I K J Parent
    (.conjL (.hyp (Or.inl rfl))) (.conjL (.conjR (.hyp (Or.inl rfl)))) (.conjR (.conjR (.hyp (Or.inl rfl))))

end PPAC.Migration.ForcingFreshOpeningInverse
