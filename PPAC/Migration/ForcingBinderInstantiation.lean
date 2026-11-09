import PPAC.Migration.ForcingOpenLift
import PPAC.Migration.Internal.AbstractBinderRename
import PPAC.Migration.Internal.SyntaxTopCodedEnvironmentFields
import PPAC.Migration.Internal.StructuralListFieldCons
import PPAC.Migration.Internal.TypedArgumentListConstruction

/-! Original lifted opening followed by actual native instantiation. Earlier
instances insert closed terms into the bound image list. Such values are not
restricted to canonical variable offsets, and may have nonstandard indices. -/
namespace PPAC.Migration.ForcingBinderInstantiation
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open StructuralListFieldSyntax (field field_rename)
open SyntaxCodedMixedTermSyntax (substituted substituted_rename)
set_option maxRecDepth 32768
attribute [local irreducible] NaturalRecursionSyntax.matrix

/-- A real native InstantiateTop fixes any closed term code, including a
nonstandard free-variable index. Equality with the actual lifted input is
sufficient; no returned code or desired equality is assumed. -/
theorem closed_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z T C P r s t u v : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s))
    (ht : Derives Γ (SyntaxTermSyntax.term w z T t))
    (hu : Derives Γ (.equal u t))
    (hi : Derives Γ (substituted w r s C T z T u v)) : Derives Γ (.equal v t) := by
  have hclosed := InstantiateOperationFrameSyntax.intro_closedParameter w T t z hz ht
  have hfree := InstantiateOperationFrameSyntax.closedParameter_free w T t hclosed
  let E := SyntaxTermSyntax.branchWitness false w T t
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch false w T t _ hfree
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have he1 := of_eq (SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename w z T C P r s Fin.castSucc) (under he E)
  have hu1 : Derives Δ (.equal u.castSucc t.castSucc) := under hu E
  have hi1 := of_eq (substituted_rename w r s C T z T u v Fin.castSucc) (under hi E)
  have hcodeU := Derives.impE (Derives.conjR (AbstractBinderRename.code_iff_equal hZ1 false w.castSucc (Fin.last m)
    t.castSucc u.castSucc hw1 (Derives.conjR hE))) hu1
  have hfields := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ1 false w.castSucc r.castSucc s.castSucc C.castSucc T.castSucc z.castSucc T.castSucc
    u.castSucc v.castSucc (Fin.last m) hw1 (SyntaxTopCodedEnvironmentTyping.instantiate_lists w.castSucc z.castSucc T.castSucc C.castSucc P.castSucc r.castSucc s.castSucc he1) hcodeU)) hi1
  have hcodeV := Derives.impE (Derives.conjL (SyntaxTopCodedEnvironmentFields.instantiate_free hZ1 w.castSucc z.castSucc T.castSucc C.castSucc
    P.castSucc r.castSucc s.castSucc (Fin.last m) v.castSucc he1 (Derives.conjL hE))) hfields
  exact Derives.impE (Derives.conjL (AbstractBinderRename.code_iff_equal hZ1 false w.castSucc (Fin.last m) t.castSucc v.castSucc hw1 (Derives.conjR hE))) hcodeV

def frame {m} (w z a f T A C R S K H P r s D : Fin m) : Formula m :=
  (omega w).conj ((empty z).conj ((SyntaxMixedImageCodeSyntax.termLists w a f z T R S).conj ((SyntaxCodedMixedBinderSyntax.lifted w R S a f z T A C K H).conj ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z T C P r s).conj ((StructuralListSyntax.consCode w P R D).conj (SyntaxMixedImageCodeSyntax.termList w A z T D))))))

theorem frame_rename {m l} (w z a f T A C R S K H P r s D : Fin m) (ρ : Fin m → Fin l) :
    (frame w z a f T A C R S K H P r s D).rename ρ = frame (ρ w) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ D) := by
  simp only [frame, Formula.rename, omega_rename, empty_rename, SyntaxMixedImageCodeSyntax.termLists_rename,
    SyntaxCodedMixedBinderSyntax.lifted_rename, SyntaxTopCodedEnvironmentSyntax.instantiateCoded_rename, StructuralListSyntax.consCode_rename, SyntaxMixedImageCodeSyntax.termList_rename]

def path {m} (w z _a f T A C _R S K H _P r s D x u v y : Fin m) : Formula m :=
  (substituted w K H A f C T x u).conj
    ((substituted w r s C T z T u v).conj (substituted w D S A f z T x y))

theorem path_rename {m l} (w z a f T A C R S K H P r s D x u v y : Fin m) (ρ : Fin m → Fin l) :
    (path w z a f T A C R S K H P r s D x u v y).rename ρ = path (ρ w) (ρ z) (ρ a) (ρ f) (ρ T) (ρ A) (ρ C) (ρ R) (ρ S) (ρ K) (ρ H) (ρ P) (ρ r) (ρ s) (ρ D) (ρ x) (ρ u) (ρ v) (ρ y) := by
  simp only [path, Formula.rename, substituted_rename]

private theorem free_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D x u v y i : Fin m)
    (hf : Derives Γ (frame w z a f T A C R S K H P r s D)) (hp : Derives Γ (path w z a f T A C R S K H P r s D x u v y))
    (hc : Derives Γ (SyntaxVariableSyntax.code false w i x))
    : Derives Γ (.equal v y) := by
  have f0 := (Derives.conjL hf)
  have f1 := (Derives.conjL (Derives.conjR hf))
  have f2 := (Derives.conjL (Derives.conjR (Derives.conjR hf)))
  have f3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have f4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))
  have f5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have f6 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have p0 := (Derives.conjL hp)
  have p1 := (Derives.conjL (Derives.conjR hp))
  have p2 := (Derives.conjR (Derives.conjR hp))
  have hDirectLists := Derives.conjI f6 (Derives.conjR f2)
  have hLiftLists := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H f3
  have hD := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w D S A f z T x y i f0 hDirectLists hc)) p2
  have hL := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ false w K H A f C T x u i f0 hLiftLists hc)) p0
  have hs : Derives Γ (ForcingOpenLift.step false i i) := .impI (.hyp (Or.inl rfl))
  have heq := Derives.impE (Derives.conjL (ForcingOpenLift.old_fields_from_lists hZ false w z a f T A C R S K H i i y u
    f0 f1 f2 f3 (Derives.conjL hD) (Derives.conjR hD) hs)) hL
  have ht := SyntaxMixedImageCodeFields.field_type w f z T S i y (Derives.conjR f2) (Derives.conjL hD) (Derives.conjR hD)
  exact closed_output hZ w z T C P r s y u v f0 f1 f4 ht heq p1

private theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D x u v y i : Fin m)
    (hf : Derives Γ (frame w z a f T A C R S K H P r s D)) (hp : Derives Γ (path w z a f T A C R S K H P r s D x u v y))
    (hc : Derives Γ (SyntaxVariableSyntax.code true w i x))
    (hi : Derives Γ (empty i))
    : Derives Γ (.equal v y) := by
  have f0 := (Derives.conjL hf)
  have f1 := (Derives.conjL (Derives.conjR hf))
  have f2 := (Derives.conjL (Derives.conjR (Derives.conjR hf)))
  have f3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have f4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))
  have f5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have f6 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have p0 := (Derives.conjL hp)
  have p1 := (Derives.conjL (Derives.conjR hp))
  have p2 := (Derives.conjR (Derives.conjR hp))
  have hDirectLists := Derives.conjI f6 (Derives.conjR f2)
  have hLiftLists := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H f3
  have hD := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ true w D S A f z T x y i f0 hDirectLists hc)) p2
  have hiz := OmegaUniversal.empty_unique i z (ZFContext.arithmetic hZ).base.extensionality hi f1
  have hcodeZ := SyntaxVariableImagePoint.code_subst_index true w i x z hiz hc
  have hL := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ true w K H A f C T x u z f0 hLiftLists hcodeZ)) p0
  have hHead := ForcingOpenLift.zero_code_from_lists hZ w z a f T A C R S K H u f0 f1 f2 f3 hL
  have hN := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ true w r s C T z T u v z f0
    (SyntaxTopCodedEnvironmentTyping.instantiate_lists w z T C P r s f4) hHead)) p1
  have hv := Derives.impE (Derives.conjL (SyntaxTopCodedEnvironmentFields.instantiate_zero hZ w z T C P r s z v f0 f4 f1)) hN
  have htP := Derives.conjL (SyntaxTopCodedEnvironmentTyping.instantiate_input w z T C P r s f4)
  have hPn := SyntaxTerms.range hZ w z T P f0 htP
  have hRn := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjL f2))))
  have hy := StructuralListFieldCons.zero_point hZ w P R D i y f0 hPn hRn f5 hi (Derives.conjR hD)
  exact eq_trans hv (eq_symm hy)

private theorem successor_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D x u v y i j : Fin m)
    (hf : Derives Γ (frame w z a f T A C R S K H P r s D)) (hp : Derives Γ (path w z a f T A C R S K H P r s D x u v y))
    (hc : Derives Γ (SyntaxVariableSyntax.code true w i x))
    (hj : Derives Γ (.mem j w)) (hij : Derives Γ (successor i j))
    : Derives Γ (.equal v y) := by
  have f0 := (Derives.conjL hf)
  have f1 := (Derives.conjL (Derives.conjR hf))
  have f2 := (Derives.conjL (Derives.conjR (Derives.conjR hf)))
  have f3 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR hf))))
  have f4 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf)))))
  have f5 := (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have f6 := (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR (Derives.conjR hf))))))
  have p0 := (Derives.conjL hp)
  have p1 := (Derives.conjL (Derives.conjR hp))
  have p2 := (Derives.conjR (Derives.conjR hp))
  have hDirectLists := Derives.conjI f6 (Derives.conjR f2)
  have hLiftLists := SyntaxCodedMixedBinderTyping.output_lists w R S a f z T A C K H f3
  have hD := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ true w D S A f z T x y i f0 hDirectLists hc)) p2
  have htP := Derives.conjL (SyntaxTopCodedEnvironmentTyping.instantiate_input w z T C P r s f4)
  have hPn := SyntaxTerms.range hZ w z T P f0 htP
  have hRn := Derives.conjL (Derives.conjL (Derives.conjR (Derives.conjR (Derives.conjL f2))))
  have hTail := StructuralListFieldCons.successor_forward hZ w P R D j i y f0 hPn hRn hj hij f5 (Derives.conjR hD)
  have hA := Derives.conjL (Derives.conjR (SyntaxCodedMixedBinderTyping.input_of_lifted w R S a f z T A C K H f3))
  have hja := SyntaxIndexLiftOrder.predecessor_member hZ w a A i j f0 (Derives.conjL (Derives.conjL f2)) hA (Derives.conjL hD) hij
  have hL := Derives.impE (Derives.conjL (SyntaxCodedMixedTermFields.at_field hZ true w K H A f C T x u i f0 hLiftLists hc)) p0
  have heq := Derives.impE (Derives.conjL (ForcingOpenLift.old_fields_from_lists hZ true w z a f T A C R S K H j i y u
    f0 f1 f2 f3 hja hTail hij)) hL
  have ht := SyntaxMixedImageCodeFields.field_type w a z T R j y (Derives.conjL f2) hja hTail
  exact closed_output hZ w z T C P r s y u v f0 f1 f4 ht heq p1

/-- Collapse one REAL lifted opening / native instance against the direct
prefixed bound table. Index cases use the existing internal omega theorem,
not host Nat or an external-standard bound. -/
theorem term {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z a f T A C R S K H P r s D x u v y : Fin m)
    (hf : Derives Γ (frame w z a f T A C R S K H P r s D))
    (hp : Derives Γ (path w z a f T A C R S K H P r s D x u v y)) : Derives Γ (.equal v y) := by
  have ht := SyntaxCodedMixedTermTyping.source_type w D S A f z T x y (Derives.conjR (Derives.conjR hp))
  apply Derives.disjE (Derives.conjR ht)
  · let E := SyntaxTermSyntax.branch true w A x
    let B := SyntaxTermSyntax.branchWitness true w A x
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch true w A x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hf1 := of_eq (frame_rename w z a f T A C R S K H P r s D Fin.castSucc) (under (add hf E) B)
    have hp1 := of_eq (path_rename w z a f T A C R S K H P r s D x u v y Fin.castSucc) (under (add hp E) B)
    have hw1 := Derives.conjL hf1
    have ht1 := SyntaxCodedMixedTermTyping.source_type w.castSucc D.castSucc S.castSucc A.castSucc f.castSucc z.castSucc T.castSucc x.castSucc y.castSucc
      (Derives.conjR (Derives.conjR hp1))
    have hi := StructuralListTraceOrder.member_member hZ1 w.castSucc (Fin.last m) A.castSucc hw1 (Derives.conjL (Derives.conjL ht1)) (Derives.conjL hB)
    have hs := OmegaStructureAlgebra.decomposition_at w.castSucc (Fin.last m)
      (OmegaStructureInduction.decomposition w.castSucc (ZFContext.separation hZ1 OmegaStructureSyntax.splitMatrix) hw1) hi
    apply Derives.disjE hs
    · exact zero_point (ZFContext.add hZ1 (empty (Fin.last m))) w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc
        R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc D.castSucc x.castSucc u.castSucc v.castSucc y.castSucc (Fin.last m)
        (add hf1 _) (add hp1 _) (add (Derives.conjR hB) _) (.hyp (Or.inl rfl))
    · let E2 := OmegaStructureSyntax.predecessor w.castSucc (Fin.last m)
      let B2 := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (successor (Fin.last m).castSucc (Fin.last (m+1)))
      let Ξ := Context.add B2 (Context.image Formula.raise (Context.add E2 Δ))
      apply Derives.exE (p := B2) (.hyp (Or.inl rfl))
      have hB2 : Derives Ξ B2 := .hyp (Or.inl rfl)
      have hZ2 := ZFContext.under (ZFContext.add hZ1 E2) B2
      have hf2 := of_eq (frame_rename w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc
        R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc D.castSucc Fin.castSucc) (under (add hf1 E2) B2)
      have hp2 := of_eq (path_rename w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc
        R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc D.castSucc x.castSucc u.castSucc v.castSucc y.castSucc Fin.castSucc) (under (add hp1 E2) B2)
      have hc2 := of_eq (SyntaxVariableSyntax.code_rename true w.castSucc (Fin.last m) x.castSucc Fin.castSucc) (under (add (Derives.conjR hB) E2) B2)
      exact successor_point hZ2 w.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc T.castSucc.castSucc
        A.castSucc.castSucc C.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc K.castSucc.castSucc H.castSucc.castSucc P.castSucc.castSucc
        r.castSucc.castSucc s.castSucc.castSucc D.castSucc.castSucc x.castSucc.castSucc u.castSucc.castSucc v.castSucc.castSucc y.castSucc.castSucc
        (Fin.last m).castSucc (Fin.last (m+1)) hf2 hp2 hc2 (Derives.conjL hB2) (Derives.conjR hB2)
  · let E := SyntaxTermSyntax.branch false w f x
    let B := SyntaxTermSyntax.branchWitness false w f x
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply SyntaxTermSyntax.eliminate_branch false w f x _ (.hyp (Or.inl rfl))
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hf1 := of_eq (frame_rename w z a f T A C R S K H P r s D Fin.castSucc) (under (add hf E) B)
    have hp1 := of_eq (path_rename w z a f T A C R S K H P r s D x u v y Fin.castSucc) (under (add hp E) B)
    exact free_point (ZFContext.under (ZFContext.add hZ E) B) w.castSucc z.castSucc a.castSucc f.castSucc T.castSucc A.castSucc C.castSucc
      R.castSucc S.castSucc K.castSucc H.castSucc P.castSucc r.castSucc s.castSucc D.castSucc x.castSucc u.castSucc v.castSucc y.castSucc (Fin.last m)
      hf1 hp1 (Derives.conjR hB)

def sentence {m} (w z a f T A C R S K H P r s D x u v y : Fin m) : Source.Sentence :=
  (((frame w z a f T A C R S K H P r s D).conj (path w z a f T A C R S K H P r s D x u v y)).imp (.equal v y)).close

theorem kernel_certificate {m} (w z a f T A C R S K H P r s D x u v y : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w z a f T A C R S K H P r s D x u v y)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  let E := (frame w z a f T A C R S K H P r s D).conj (path w z a f T A C R S K H P r s D x u v y)
  let Δ := Context.add E (Source.SetLanguage.ZF.at m)
  have h : Derives Δ E := .hyp (Or.inl rfl)
  exact term (ZFContext.add (ZFContext.source_ZF m) E) w z a f T A C R S K H P r s D x u v y (Derives.conjL h) (Derives.conjR h)

end PPAC.Migration.ForcingBinderInstantiation
