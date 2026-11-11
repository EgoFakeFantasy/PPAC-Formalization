import PPAC.Migration.ForcingReindexedImages
import PPAC.Migration.ForcingFreshBackground
import PPAC.Migration.Internal.SyntaxWeakenFreeLogicalInternal
import PPAC.Migration.Internal.SyntaxWeakenFreeOutput

/-! Actual original first-free0 weakening of source term-image records.
All index codes, their real graphs and the six original pushed-image witnesses
are generated inside the object theory. Reuse full formula covariance. -/
namespace PPAC.Migration.ForcingWeakenedImages
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def images {m} (v : Fin 10 → Fin m) : Fin 6 → Fin m :=
  Fin.cases (v 4) (Fin.cases (v 5) (Fin.cases (v 6) (Fin.cases (v 7) (SyntaxAtomSyntax.two (v 8) (v 9)))))
private theorem images_map {m l} (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (fun i => ρ (images v i)) = images (fun i => ρ (v i)) := by
  funext i
  rcases i with ⟨i,hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def input {m} (w a b c d D R S : Fin m) : Formula m :=
  (omega w).conj ((successor D d).conj (SyntaxMixedImageCodeSyntax.termLists w a b c d R S))
theorem input_rename {m l} (w a b c d D R S : Fin m) (ρ : Fin m → Fin l) :
    (input w a b c d D R S).rename ρ = input (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ D) (ρ R) (ρ S) := by
  simp only [input, Formula.rename, omega_rename, successor_rename, SyntaxMixedImageCodeSyntax.termLists_rename]

def operations {m} (w c d D Ib Jb I J : Fin m) : Formula m :=
  (SyntaxIdentityMapSyntax.identityCode w c Ib).conj
    ((SyntaxFreeShiftSyntax.shiftCode w d D Jb).conj
      ((SyntaxMapCodeSyntax.encoded w I c c Ib).conj (SyntaxMapCodeSyntax.encoded w J d D Jb)))
theorem operations_rename {m l} (w c d D Ib Jb I J : Fin m) (ρ : Fin m → Fin l) :
    (operations w c d D Ib Jb I J).rename ρ = operations (ρ w) (ρ c) (ρ d) (ρ D) (ρ Ib) (ρ Jb) (ρ I) (ρ J) := by
  simp only [operations, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename,
    SyntaxFreeShiftSyntax.shiftCode_rename, SyntaxMapCodeSyntax.encoded_rename]

def data {m} (w a b c d D R S : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (input w a b c d D R S).conj ((operations w c d D (v 0) (v 1) (v 2) (v 3)).conj
    (ForcingReindexedImages.data w a b c d c D R S (v 2) (v 3) (images v)))
theorem data_rename {m l} (w a b c d D R S : Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (data w a b c d D R S v).rename ρ = data (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ D) (ρ R) (ρ S) (fun i => ρ (v i)) := by
  simp only [data, Formula.rename, input_rename, operations_rename, ForcingReindexedImages.data_rename, images_map]

def body {m} (w a b c d D R S : Fin m) : Formula (m+10) :=
  data (old 10 w) (old 10 a) (old 10 b) (old 10 c) (old 10 d) (old 10 D) (old 10 R) (old 10 S) (slot 10)
def produced {m} (w a b c d D R S : Fin m) : Formula m := existsMany 10 (body w a b c d D R S)
theorem produced_rename {m l} (w a b c d D R S : Fin m) (ρ : Fin m → Fin l) :
    (produced w a b c d D R S).rename ρ = produced (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ D) (ρ R) (ρ S) := by
  simp only [produced, existsMany_rename, body, data_rename, lift_old, lift_slot]

private theorem at_operations {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S Ib Jb I J : Fin m)
    (hi : Derives Γ (input w a b c d D R S)) (hp : Derives Γ (operations w c d D Ib Jb I J)) :
    Derives Γ (produced w a b c d D R S) := by
  have hm : Derives Γ (SyntaxIndexMapSyntax.maps w I J c d c D) :=
    .conjI (.conjR (.conjL (.conjR (.conjR hp)))) (.conjR (.conjR (.conjR (.conjR hp))))
  let E := ForcingReindexedImages.data (old 6 w) (old 6 a) (old 6 b) (old 6 c) (old 6 d) (old 6 c) (old 6 D)
    (old 6 R) (old 6 S) (old 6 I) (old 6 J) (slot 6)
  let Δ := Context.add E (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 E _
    (ForcingReindexedImages.produce hZ w a b c d c D R S I J (.conjL hi) hm (.conjR (.conjR hi)))
  have hi6 := of_eq (input_rename w a b c d D R S (old 6)) (HornBinderRules.under_body 6 hi E)
  have hp6 := of_eq (operations_rename w c d D Ib Jb I J (old 6)) (HornBinderRules.under_body 6 hp E)
  let v : Fin 10 → Fin (m+6) := Fin.cases (old 6 Ib) (Fin.cases (old 6 Jb) (Fin.cases (old 6 I) (Fin.cases (old 6 J) (slot 6))))
  have hd : Derives Δ (data (old 6 w) (old 6 a) (old 6 b) (old 6 c) (old 6 d) (old 6 D) (old 6 R) (old 6 S) v) :=
    .conjI hi6 (.conjI hp6 (.hyp (Or.inl rfl)))
  have ho : Derives Δ (produced (old 6 w) (old 6 a) (old 6 b) (old 6 c) (old 6 d) (old 6 D) (old 6 R) (old 6 S)) := by
    apply HornBinderRules.intro_many 10 _ v
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  exact of_eq (produced_rename w a b c d D R S (old 6)).symm ho

private theorem at_identity_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S Ib Jb I : Fin m) (hi : Derives Γ (input w a b c d D R S))
    (hIb : Derives Γ (SyntaxIdentityMapSyntax.identityCode w c Ib))
    (hJb : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w d D Jb))
    (hI : Derives Γ (SyntaxMapCodeSyntax.encoded w I c c Ib)) : Derives Γ (produced w a b c d D R S) := by
  let E := (SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) d.castSucc D.castSucc Jb.castSucc).conj
    (SyntaxFreeShiftSyntax.shiftMap w.castSucc d.castSucc D.castSucc (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hJb
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hp : Derives Δ (operations w.castSucc c.castSucc d.castSucc D.castSucc Ib.castSucc Jb.castSucc I.castSucc (Fin.last m)) :=
    .conjI (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w c Ib Fin.castSucc) (under hIb E))
      (.conjI (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w d D Jb Fin.castSucc) (under hJb E))
        (.conjI (of_eq (SyntaxMapCodeSyntax.encoded_rename w I c c Ib Fin.castSucc) (under hI E)) (.conjL hE)))
  have ho := at_operations (ZFContext.under hZ E) w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc D.castSucc R.castSucc S.castSucc
    Ib.castSucc Jb.castSucc I.castSucc (Fin.last m)
    (of_eq (input_rename w a b c d D R S Fin.castSucc) (under hi E)) hp
  exact of_eq (produced_rename w a b c d D R S Fin.castSucc).symm ho

private theorem at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S Ib Jb : Fin m) (hi : Derives Γ (input w a b c d D R S))
    (hIb : Derives Γ (SyntaxIdentityMapSyntax.identityCode w c Ib))
    (hJb : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w d D Jb)) : Derives Γ (produced w a b c d D R S) := by
  let E := (SyntaxMapCodeSyntax.encoded w.castSucc (Fin.last m) c.castSucc c.castSucc Ib.castSucc).conj
    (SyntaxRenameTermIdentity.diagonal (Fin.last m))
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hIb
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := at_identity_graph (ZFContext.under hZ E) w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc D.castSucc R.castSucc S.castSucc
    Ib.castSucc Jb.castSucc (Fin.last m)
    (of_eq (input_rename w a b c d D R S Fin.castSucc) (under hi E))
    (of_eq (SyntaxIdentityMapSyntax.identityCode_rename w c Ib Fin.castSucc) (under hIb E))
    (of_eq (SyntaxFreeShiftSyntax.shiftCode_rename w d D Jb Fin.castSucc) (under hJb E)) (.conjL hE)
  exact of_eq (produced_rename w a b c d D R S Fin.castSucc).symm ho

/-- Ten actual operation witnesses from typed source images and successor;
no expected new images, covariance law or formula output is supplied. -/
theorem produce {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c d D R S : Fin m)
    (hi : Derives Γ (input w a b c d D R S)) : Derives Γ (produced w a b c d D R S) := by
  have ht := Derives.conjR (.conjR hi)
  have hc := Derives.conjL (.conjL (.conjR (.conjL ht)))
  have hd := Derives.conjR (.conjL (.conjR (.conjL ht)))
  let E := SyntaxWeakenFreeLogicalInternal.codeBody w c d D
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _
    (SyntaxWeakenFreeLogicalInternal.actual_codes_exists hZ w c d D (.conjL hi) hc hd (.conjL (.conjR hi)))
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := at_codes (HornBinderRules.zf_body 2 hZ E) (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d)
    (old 2 D) (old 2 R) (old 2 S) (slot 2 0) (slot 2 1)
    (of_eq (input_rename w a b c d D R S (old 2)) (HornBinderRules.under_body 2 hi E)) (.conjL hE) (.conjR hE)
  exact of_eq (produced_rename w a b c d D R S (old 2)).symm ho

def queryInput {m} (w a b c d D R S n u o : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  (data w a b c d D R S v).conj
    ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n u).conj
      (SyntaxMixedFormulaJudgmentSyntax.substituted w (v 8) (v 9) a b c D n o))
theorem queryInput_rename {m l} (w a b c d D R S n u o : Fin m) (v : Fin 10 → Fin m) (ρ : Fin m → Fin l) :
    (queryInput w a b c d D R S n u o v).rename ρ =
      queryInput (ρ w) (ρ a) (ρ b) (ρ c) (ρ d) (ρ D) (ρ R) (ρ S) (ρ n) (ρ u) (ρ o) (fun i => ρ (v i)) := by
  simp only [queryInput, Formula.rename, data_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

private theorem at_realization {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S n u o P Q F G : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Γ (queryInput w a b c d D R S n u o v))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w (v 0) (v 1) P Q c d c D))
    (hr : Derives Γ (IndexTermRenameTransportSyntax.realization w (v 2) (v 3) F G c d c D P Q)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w c d D u o) := by
  have hData := Derives.conjL hi
  have hw := Derives.conjL (.conjL hData)
  have hOps := Derives.conjL (.conjR hData)
  have hOld := Derives.conjL (.conjR hi)
  have ht := SyntaxMixedFormulaJudgment.target_type w R S a b c d n u hOld
  have hx := SyntaxRenameOutputInduction.actual_exists hZ w (v 0) (v 1) c d c D u hw
    (.conjI ht (.conjI (SyntaxIdentityCode.map_code _ _ _ (.conjL hOps))
      (SyntaxFreeShiftCode.map_code _ _ _ _ (.conjL (.conjR hOps)))))
  let E := SyntaxRenameJudgmentSyntax.renamed w.castSucc (v 0).castSucc (v 1).castSucc c.castSucc d.castSucc c.castSucc D.castSucc u.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hx
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ E
  have h1 := of_eq (queryInput_rename w a b c d D R S n u o v Fin.castSucc) (under hi E)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have he1 := of_eq (IndexTermImageCodeSyntax.environment_rename w (v 0) (v 1) P Q c d c D Fin.castSucc) (under he E)
  have hr1 := of_eq (IndexTermRenameTransportSyntax.realization_rename w (v 2) (v 3) F G c d c D P Q Fin.castSucc) (under hr E)
  have hImage := Derives.conjR (.conjR (.conjL h1))
  have hSequential := IndexFormulaRenameInduction.forward hZ1 w.castSucc (v 0).castSucc (v 1).castSucc P.castSucc Q.castSucc
    c.castSucc d.castSucc c.castSucc D.castSucc u.castSucc (Fin.last m) hw1 he1 hE
  have hCompare := ForcingReindexedImages.compare hZ1
    w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc c.castSucc D.castSucc R.castSucc S.castSucc
    (v 2).castSucc (v 3).castSucc F.castSucc G.castSucc P.castSucc Q.castSucc n.castSucc u.castSucc (Fin.last m) o.castSucc
    (images (fun i => (v i).castSucc))
    (.conjI hw1 (.conjI hImage (.conjI hr1 (.conjI (.conjL (.conjR h1)) (.conjI hSequential (.conjR (.conjR h1)))))))
  have hOps1 := Derives.conjL (.conjR (.conjL h1))
  have hWeak := SyntaxWeakenFreeSyntax.intro_weakened w.castSucc c.castSucc d.castSucc D.castSucc u.castSucc (Fin.last m)
    (v 0).castSucc (v 1).castSucc (.conjL hOps1) (.conjL (.conjR hOps1)) hE
  have ho := SyntaxWeakenFreeSyntax.subst_q _ _ _ _ _ _ _ hCompare hWeak
  exact of_eq (SyntaxWeakenFreeSyntax.weakened_rename w c d D u o Fin.castSucc).symm ho

private theorem at_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S n u o P Q : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Γ (queryInput w a b c d D R S n u o v))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w (v 0) (v 1) P Q c d c D)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w c d D u o) := by
  have hOps := Derives.conjL (.conjR (.conjL hi))
  let E := IndexTermRenameTransportSyntax.realization (old 2 w) (old 2 (v 2)) (old 2 (v 3)) (slot 2 0) (slot 2 1)
    (old 2 c) (old 2 d) (old 2 c) (old 2 D) (old 2 P) (old 2 Q)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _
    (IndexTermImageEnvironment.realization_exists hZ w (v 0) (v 1) P Q c d c D (v 2) (v 3) he
      (.conjL (.conjR (.conjR hOps))) (.conjR (.conjR (.conjR hOps))))
  have ho := at_realization (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 D) (old 2 R) (old 2 S)
    (old 2 n) (old 2 u) (old 2 o) (old 2 P) (old 2 Q) (slot 2 0) (slot 2 1) (fun i => old 2 (v i))
    (of_eq (queryInput_rename w a b c d D R S n u o v (old 2)) (HornBinderRules.under_body 2 hi E))
    (of_eq (IndexTermImageCodeSyntax.environment_rename w (v 0) (v 1) P Q c d c D (old 2)) (HornBinderRules.under_body 2 he E))
    (.hyp (Or.inl rfl))
  exact of_eq (SyntaxWeakenFreeSyntax.weakened_rename w c d D u o (old 2)).symm ho

/-- The desired original weakened relation is the CONCLUSION, not a
premise. Both actual mixed-image codes, both realization graphs and the
actual renamed output are generated/eliminated; compare discharges its
four identity witnesses and reuses the completed full formula cancellation. -/
theorem from_queries {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b c d D R S n u o : Fin m) (v : Fin 10 → Fin m)
    (hi : Derives Γ (queryInput w a b c d D R S n u o v)) :
    Derives Γ (SyntaxWeakenFreeSyntax.weakened w c d D u o) := by
  have hOps := Derives.conjL (.conjR (.conjL hi))
  have hw := Derives.conjL (.conjL (.conjL hi))
  let E := IndexTermImageCodeSyntax.environment (old 2 w) (old 2 (v 0)) (old 2 (v 1)) (slot 2 0) (slot 2 1)
    (old 2 c) (old 2 d) (old 2 c) (old 2 D)
  let Δ := Context.add E (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 E _
    (IndexTermImageEnvironment.exists_environment hZ w (v 0) (v 1) c d c D hw
      (SyntaxIdentityCode.map_code _ _ _ (.conjL hOps))
      (SyntaxFreeShiftCode.map_code _ _ _ _ (.conjL (.conjR hOps))))
  have ho := at_environment (HornBinderRules.zf_body 2 hZ E)
    (old 2 w) (old 2 a) (old 2 b) (old 2 c) (old 2 d) (old 2 D) (old 2 R) (old 2 S)
    (old 2 n) (old 2 u) (old 2 o) (slot 2 0) (slot 2 1) (fun i => old 2 (v i))
    (of_eq (queryInput_rename w a b c d D R S n u o v (old 2)) (HornBinderRules.under_body 2 hi E)) (.hyp (Or.inl rfl))
  exact of_eq (SyntaxWeakenFreeSyntax.weakened_rename w c d D u o (old 2)).symm ho

/-- Consume the actual source query comparison in the existing guarded
forall proof. The original weakened-answer premise is removed. Matching the
second actual query to the SAME canonical Global remains the source caller's
computational obligation, explicitly retained by queryInput. -/
theorem generalize_layout {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (test : Formula 1)
    (w a f z b A B R S n G Extra Pre Tail : Fin m) (v : Fin 10 → Fin m) (H ctx : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hA : Derives Γ (successor A z))
    (hq : Derives Γ (queryInput w a f z b B R S n G (ctx 3) v))
    (hp : Derives Γ (ForcingProofUniversal.resultData test w z b A B Extra Pre Tail H ctx)) :
    Derives Γ (ForcingProofUniversal.guarded test w z b A B G (ctx 3) (ctx 4) Tail) :=
  ForcingFreshBackground.generalize_layout hZ test w z b A B G Extra Pre Tail H ctx hw hz hA
    (from_queries hZ w a f z b B R S n G (ctx 3) v hq) hp

def sentence {m} (w a b c d D R S : Fin m) : Source.Sentence :=
  ((input w a b c d D R S).imp (produced w a b c d D R S)).close
theorem kernel_certificate {m} (w a b c d D R S : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a b c d D R S)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact produce (ZFContext.add (ZFContext.source_ZF m) _) w a b c d D R S (.hyp (Or.inl rfl))

def querySentence {m} (w a b c d D R S n u o : Fin m) (v : Fin 10 → Fin m) : Source.Sentence :=
  ((queryInput w a b c d D R S n u o v).imp (SyntaxWeakenFreeSyntax.weakened w c d D u o)).close
theorem query_kernel_certificate {m} (w a b c d D R S n u o : Fin m) (v : Fin 10 → Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (querySentence w a b c d D R S n u o v)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact from_queries (ZFContext.add (ZFContext.source_ZF m) _) w a b c d D R S n u o v (.hyp (Or.inl rfl))


/-- Change only the decoded bound graph, its pushed graph and bound list. -/
def withBound {m} (v : Fin 10 → Fin m) (r g T : Fin m) : Fin 10 → Fin m :=
  Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases (v 3)
    (Fin.cases r (Fin.cases (v 5) (Fin.cases g (Fin.cases (v 7) (SyntaxAtomSyntax.two T (v 9)))))))))

theorem withBound_map {m l} (v : Fin 10 → Fin m) (r g T : Fin m) (rho : Fin m → Fin l) :
    (fun i => rho (withBound v r g T i)) =
      withBound (fun i => rho (v i)) (rho r) (rho g) (rho T) := by
  funext ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def boundBody {m} (w a f c d D T S : Fin m) (v : Fin 10 → Fin m) : Formula (m+3) :=
  data (old 3 w) (old 3 a) (old 3 f) (old 3 c) (old 3 d) (old 3 D) (old 3 T) (old 3 S)
    (withBound (fun i => old 3 (v i)) (slot 3 0) (slot 3 1) (slot 3 2))

def boundRebased {m} (w a f c d D T S : Fin m) (v : Fin 10 → Fin m) : Formula m :=
  existsMany 3 (boundBody w a f c d D T S v)

theorem boundRebased_rename {m l} (w a f c d D T S : Fin m) (v : Fin 10 → Fin m) (rho : Fin m → Fin l) :
    (boundRebased w a f c d D T S v).rename rho =
      boundRebased (rho w) (rho a) (rho f) (rho c) (rho d) (rho D) (rho T) (rho S) (fun i => rho (v i)) := by
  simp only [boundRebased, boundBody, existsMany_rename, data_rename, withBound_map, lift_old, lift_slot]

/-- Keep the existing index maps and the whole free column. Run the original
graph decoder, push and encoder only on the independent bound list. -/
theorem rebase_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a0 a f c d D R S T : Fin m) (v : Fin 10 → Fin m)
    (hv : Derives Γ (data w a0 f c d D R S v))
    (ht : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a c d T)) :
    Derives Γ (boundRebased w a f c d D T S v) := by
  let E := SyntaxMixedImageCodeSyntax.encoded (old 1 w) (slot 1 0)
    (old 1 a) (old 1 c) (old 1 d) (old 1 T)
  let Γ1 := Context.add E (raisedContext 1 Γ)
  have hw := Derives.conjL (.conjL hv)
  apply HornBinderRules.eliminate_many 1 E _ (SyntaxMixedImageCodeExistence.exists_graph hZ w a c d T hw ht)
  have hE : Derives Γ1 E := .hyp (Or.inl rfl)
  have hZ1 := HornBinderRules.zf_body 1 hZ E
  have hw1 := of_eq (omega_rename w (old 1)) (HornBinderRules.under_body 1 hw E)
  have ops := Derives.conjL (.conjR hv)
  have maps : Derives Γ (SyntaxIndexMapSyntax.maps w (v 2) (v 3) c d c D) :=
    .conjI (.conjR (.conjL (.conjR (.conjR ops)))) (.conjR (.conjR (.conjR (.conjR ops))))
  have maps1 := of_eq (SyntaxIndexMapSyntax.maps_rename w (v 2) (v 3) c d c D (old 1))
    (HornBinderRules.under_body 1 maps E)
  let P := SyntaxTermImagePushSyntax.pushed (old 1 (old 1 w)) (old 1 (old 1 (v 2))) (old 1 (old 1 (v 3)))
    (old 1 (old 1 c)) (old 1 (old 1 d)) (old 1 (old 1 c)) (old 1 (old 1 D))
    (old 1 (slot 1 0)) (old 1 (old 1 a)) (slot 1 0)
  let Γ2 := Context.add P (raisedContext 1 Γ1)
  apply HornBinderRules.eliminate_many 1 P _ (SyntaxTermImagePushGraph.exists_push hZ1
    (old 1 w) (old 1 (v 2)) (old 1 (v 3)) (old 1 c) (old 1 d) (old 1 c) (old 1 D)
    (slot 1 0) (old 1 a) hw1 (.conjL hE) maps1)
  have hP : Derives Γ2 P := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 1 hZ1 P
  let rho2 := fun i : Fin m => old 1 (old 1 i)
  have hw2 := of_eq (omega_rename (old 1 w) (old 1)) (HornBinderRules.under_body 1 hw1 P)
  let C := SyntaxMixedImageCodeSyntax.encoded (old 1 (rho2 w)) (old 1 (slot 1 0))
    (old 1 (rho2 a)) (old 1 (rho2 c)) (old 1 (rho2 D)) (slot 1 0)
  let Γ3 := Context.add C (raisedContext 1 Γ2)
  apply HornBinderRules.eliminate_many 1 C _ (SyntaxMixedImageCodeExistence.exists_code hZ2
    (rho2 w) (slot 1 0) (rho2 a) (rho2 c) (rho2 D) hw2 (.conjL (.conjR (.conjR hP))))
  have hC : Derives Γ3 C := .hyp (Or.inl rfl)
  let rho := fun i : Fin m => old 1 (rho2 i)
  let vv := fun i => rho (v i)
  let r : Fin (((m+1)+1)+1) := old 1 (old 1 (slot 1 0))
  let g : Fin (((m+1)+1)+1) := old 1 (slot 1 0)
  let T' : Fin (((m+1)+1)+1) := slot 1 0
  have lift {p : Formula m} (hp : Derives Γ p) : Derives Γ3 (p.rename rho) := by
    simpa only [rho, rho2, rename_comp] using
      HornBinderRules.under_body 1 (HornBinderRules.under_body 1 (HornBinderRules.under_body 1 hp E) P) C
  have base : Derives Γ3 (data (rho w) (rho a0) (rho f) (rho c) (rho d) (rho D)
      (rho R) (rho S) vv) := by
    simpa only [data_rename, vv] using lift hv
  have t : Derives Γ3 (SyntaxMixedImageCodeSyntax.termList (rho w) (rho a) (rho c) (rho d) (rho T)) := by
    simpa only [SyntaxMixedImageCodeSyntax.termList_rename] using lift ht
  have er : Derives Γ3 (SyntaxMixedImageCodeSyntax.encoded (rho w) r (rho a) (rho c) (rho d) (rho T)) := by
    simpa only [rho, rho2, r, E, SyntaxMixedImageCodeSyntax.encoded_rename] using
      HornBinderRules.under_body 1 (HornBinderRules.under_body 1 hE P) C
  have push : Derives Γ3 (SyntaxTermImagePushSyntax.pushed (rho w) (vv 2) (vv 3) (rho c) (rho d)
      (rho c) (rho D) r (rho a) g) := by
    simpa only [rho, rho2, vv, r, g, P, SyntaxTermImagePushSyntax.pushed_rename] using
      HornBinderRules.under_body 1 hP C
  have data' : Derives Γ3 (data (rho w) (rho a) (rho f) (rho c) (rho d) (rho D) (rho T) (rho S)
      (withBound vv r g T')) := by
    have inp := Derives.conjL base
    have reindexed := Derives.conjR (.conjR base)
    exact .conjI
      (.conjI (.conjL inp) (.conjI (.conjL (.conjR inp)) (.conjI t (.conjR (.conjR (.conjR inp))))))
      (.conjI (.conjL (.conjR base))
        (.conjI (.conjI er (.conjR (.conjL reindexed)))
          (.conjI (.conjI push (.conjR (.conjL (.conjR reindexed)))) (.conjI hC (.conjR (.conjR (.conjR reindexed)))))))
  have out : Derives Γ3 (boundRebased (rho w) (rho a) (rho f) (rho c) (rho d) (rho D) (rho T) (rho S) vv) := by
    apply HornBinderRules.intro_many 3 _ (fun i => Fin.cases r (SyntaxAtomSyntax.two g T') i)
    exact of_eq (by simp only [boundBody, data_rename, withBound_map, assign_old, assign_slot]; rfl) data'
  simpa only [rho, rho2, vv, rename_comp, boundRebased_rename] using out

end PPAC.Migration.ForcingWeakenedImages
