import PPAC.Migration.ForcingConditionRebind
import PPAC.Migration.Internal.SyntaxMixedImageLiftUnique
import PPAC.Migration.Internal.SyntaxMixedImageCodeUnique

/-! The actual existential-child environment for pinned Force.ex. Source
scope A=a+1 has the new name at bound0. Target C=a+3 has name0, r1, q2,
then old names. Reuse two target shifts, selected free images, and the original
binder lift. All tables/lists/outputs remain object existential, not a Con proof. -/
namespace PPAC.Migration.ForcingExistChildCode
open Internal Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
set_option maxRecDepth 32768

private def keepsHead {m} (K z t : Fin m) : Formula m := .all
  ((edge K.castSucc z.castSucc (Fin.last m)).iff (.equal (Fin.last m) t.castSucc))
private theorem keepsHead_rename {m l} (K z t : Fin m) (r : Fin m → Fin l) :
    (keepsHead K z t).rename r = keepsHead (r K) (r z) (r t) := by
  simp only [keepsHead, Formula.iff, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private structure Inputs {m} (Γ : Context m) (w a A B C f N : Fin m) : Prop where
  hw : Derives Γ (omega w)
  ha : Derives Γ (.mem a w)
  hA : Derives Γ (successor A a)
  hB : Derives Γ (successor B A)
  hC : Derives Γ (successor C B)
  hn : Derives Γ (FormulaCodeSyntax.formulaCode w N A f)

private theorem underInputs {m} {Γ : Context m} {w a A B C f N : Fin m}
    (h : Inputs Γ w a A B C f N) (T : Formula (m+1)) :
    Inputs (Context.add T (Context.image Formula.raise Γ)) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc N.castSucc := by
  exact ⟨of_eq (omega_rename w Fin.castSucc) (under h.hw T), under h.ha T,
    of_eq (successor_rename A a Fin.castSucc) (under h.hA T),
    of_eq (successor_rename B A Fin.castSucc) (under h.hB T),
    of_eq (successor_rename C B Fin.castSucc) (under h.hC T),
    of_eq (FormulaCodeSyntax.formulaCode_rename w N A f Fin.castSucc) (under h.hn T)⟩
private theorem underInputs2 {m} {Γ : Context m} {w a A B C f N : Fin m}
    (h : Inputs Γ w a A B C f N) (T : Formula (m+2)) :
    Inputs (Context.add T (raisedContext 2 Γ)) (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 N) := by
  exact ⟨of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 h.hw T), HornBinderRules.under_body 2 h.ha T,
    of_eq (successor_rename A a (old 2)) (HornBinderRules.under_body 2 h.hA T),
    of_eq (successor_rename B A (old 2)) (HornBinderRules.under_body 2 h.hB T),
    of_eq (successor_rename C B (old 2)) (HornBinderRules.under_body 2 h.hC T),
    of_eq (FormulaCodeSyntax.formulaCode_rename w N A f (old 2)) (HornBinderRules.under_body 2 h.hn T)⟩
private theorem context_A {m} {Γ : Context m} {w a A B C f N : Fin m} (h : Inputs Γ w a A B C f N) :
    Derives Γ (SyntaxTermSyntax.contexts w A f) := .conjR (FormulaCodeProperties.guards w N A f h.hn)
private theorem natural_B {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {w a A B C f N : Fin m}
    (h : Inputs Γ w a A B C f N) : Derives Γ (.mem B w) :=
  OmegaStructureAlgebra.successor_member w B A (ZFContext.arithmetic hZ).base.extensionality h.hw (.conjL (context_A h)) h.hB
private theorem context_B {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {w a A B C f N : Fin m}
    (h : Inputs Γ w a A B C f N) : Derives Γ (SyntaxTermSyntax.contexts w B f) :=
  .conjI (natural_B hZ h) (.conjR (context_A h))


private def conditionFlow {m} (w R I B C f t H j : Fin m) : Formula m := (Formula.mem j f).imp (.all
  ((edge H.castSucc j.castSucc (Fin.last m)).iff
    (SyntaxRenameTermSyntax.renamed w.castSucc R.castSucc I.castSucc B.castSucc f.castSucc C.castSucc f.castSucc t.castSucc (Fin.last m))))
private theorem conditionFlow_rename {m l} (w R I B C f t H j : Fin m) (r : Fin m → Fin l) :
    (conditionFlow w R I B C f t H j).rename r = conditionFlow (r w) (r R) (r I) (r B) (r C) (r f) (r t) (r H) (r j) := by
  simp only [conditionFlow, Formula.iff, Formula.rename, edge_rename, SyntaxRenameTermSyntax.renamed_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem selected_edge {m} {Γ : Context m} (w j t f B D : Fin m)
    (hd : Derives Γ (ForcingConditionRebind.mapped w j t f B D)) (hj : Derives Γ (.mem j f)) :
    Derives Γ (edge D j t) := by
  have h := Derives.allE t (Derives.allE j (.conjR hd))
  have hi : Derives Γ ((edge D j t).iff ((Formula.mem j f).conj (ForcingConditionRebind.value w j t j t))) :=
    of_eq (by simp only [Formula.instantiate, Formula.iff,
      ForcingConditionRebind.value_rename, edge_rename, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h
  have hv : Derives Γ (ForcingConditionRebind.value w j t j t) := .disjL (.conjI (.eqRefl j) (.eqRefl t))
  exact .impE (.conjR hi) (.conjI hj hv)

private theorem condition_flow {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f R I G D t K H j : Fin m)
    (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R I G D a f B f A C t K H))
    (hd : Derives Γ (ForcingConditionRebind.mapped w j t f B D)) : Derives Γ (conditionFlow w R I B C f t H j) := by
  apply Derives.impI
  let J := Formula.mem j f
  have hj : Derives (Context.add J Γ) J := .hyp (Or.inl rfl)
  have hp := selected_edge w j t f B D (add hd J) hj
  apply Derives.allI
  have hp1 := of_eq (edge_rename D j t Fin.castSucc) (Derives.rename Fin.castSucc hp)
  have hl1 := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w R I G D a f B f A C t K H Fin.castSucc) (Derives.rename Fin.castSucc (add hl J))
  exact SyntaxMixedImageLiftFields.free_iff (ZFContext.rename (ZFContext.add hZ J) Fin.castSucc)
    w.castSucc R.castSucc I.castSucc G.castSucc D.castSucc a.castSucc f.castSucc B.castSucc f.castSucc A.castSucc C.castSucc
    t.castSucc K.castSucc H.castSucc j.castSucc t.castSucc (Fin.last m) hl1 hp1

private def data {m} (w a A B C f j N Q : Fin m) (v : Fin 12 → Fin m) : Formula m :=
  (SyntaxMixedImageHead.head w C f (v 0) (v 1)).conj ((SyntaxVariableTableSyntax.shifted true w a A f (v 2)).conj ((SyntaxFreeShiftSyntax.shiftMap w A B (v 3)).conj ((SyntaxFreeShiftSyntax.shiftMap w B C (v 4)).conj ((SyntaxIdentityMapSyntax.identityMap w f (v 5)).conj ((SyntaxTermImagePushSyntax.pushed w (v 3) (v 5) A f B f (v 2) a (v 6)).conj ((ForcingConditionRebind.mapped w j (v 1) f B (v 7)).conj ((SyntaxMixedImageLiftSyntax.lifted w (v 4) (v 5) (v 6) (v 7) a f B f A C (v 1) (v 8) (v 9)).conj ((SyntaxMixedImageCodeSyntax.encoded w (v 8) A C f (v 10)).conj ((SyntaxMixedImageCodeSyntax.encoded w (v 9) f C f (v 11)).conj ((SyntaxMixedFormulaJudgmentSyntax.substituted w (v 10) (v 11) A f C f N Q).conj ((keepsHead (v 8) (v 0) (v 1)).conj (conditionFlow w (v 4) (v 5) B C f (v 1) (v 9) j))))))))))))

private theorem data_rename {m l} (w a A B C f j N Q : Fin m) (v : Fin 12 → Fin m) (r : Fin m → Fin l) :
    (data w a A B C f j N Q v).rename r = data (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) (fun i => r (v i)) := by
  simp only [data, Formula.rename, SyntaxMixedImageHead.head_rename, SyntaxVariableTableSyntax.shifted_rename,
    SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxIdentityMapSyntax.identityMap_rename,
    SyntaxTermImagePushSyntax.pushed_rename, ForcingConditionRebind.mapped_rename,
    SyntaxMixedImageLiftSyntax.lifted_rename, SyntaxMixedImageCodeSyntax.encoded_rename,
    SyntaxMixedFormulaJudgmentSyntax.substituted_rename, keepsHead_rename, conditionFlow_rename]
private def body {m} (w a A B C f j N Q : Fin m) : Formula (m+12) :=
  data (old 12 w) (old 12 a) (old 12 A) (old 12 B) (old 12 C) (old 12 f) (old 12 j) (old 12 N) (old 12 Q) (slot 12)
def compiled {m} (w a A B C f j N Q : Fin m) : Formula m := existsMany 12 (body w a A B C f j N Q)
theorem compiled_rename {m l} (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (compiled w a A B C f j N Q).rename r = compiled (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) := by
  simp only [compiled, existsMany_rename, body, data_rename, lift_old, lift_slot]
def existsCompiled {m} (w a A B C f j N : Fin m) : Formula m := .ex
  (compiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))
private theorem existsCompiled_rename {m l} (w a A B C f j N : Fin m) (r : Fin m → Fin l) :
    (existsCompiled w a A B C f j N).rename r = existsCompiled (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) := by
  simp only [existsCompiled, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem keeps_head {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f R3 I G D t K H z : Fin m) (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (hl : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R3 I G D a f B f A C t K H)) : Derives Γ (keepsHead K z t) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (Derives.rename Fin.castSucc hz)
  have hl1 := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w R3 I G D a f B f A C t K H Fin.castSucc) (Derives.rename Fin.castSucc hl)
  exact SyntaxMixedImageLiftFields.zero_iff (ZFContext.rename hZ Fin.castSucc)
    w.castSucc R3.castSucc I.castSucc G.castSucc D.castSucc a.castSucc f.castSucc B.castSucc f.castSucc
    A.castSucc C.castSucc t.castSucc K.castSucc H.castSucc z.castSucc (Fin.last m) hl1 hw1 hz1

private theorem assemble {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2 R3 I G D K H L S: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    (h3 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w B C R3))
    (h4 : Derives Γ (SyntaxIdentityMapSyntax.identityMap w f I))
    (h5 : Derives Γ (SyntaxTermImagePushSyntax.pushed w R2 I A f B f F a G))
    (h6 : Derives Γ (ForcingConditionRebind.mapped w j t f B D))
    (h7 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R3 I G D a f B f A C t K H))
    (h8 : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w K A C f L))
    (h9 : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w H f C f S))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have hi : Derives Γ (SyntaxMixedFormulaOutputSyntax.input w L S A f C f N) := .conjI h.hn
    (.conjI (SyntaxMixedImageCodeFields.term_list w K A C f L h8) (SyntaxMixedImageCodeFields.term_list w H f C f S h9))
  have hk := keeps_head hZ w a A B C f R3 I G D t K H z h.hw (.conjL h0) h7
  have hflow := condition_flow hZ w a A B C f R3 I G D t K H j h7 h6
  let T := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc L.castSucc S.castSucc A.castSucc f.castSucc C.castSucc f.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxMixedFormulaOutputInduction.actual_exists hZ w L S A f C f N h.hw hi)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 Fin.castSucc) (under h2 T)
  have h31 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C R3 Fin.castSucc) (under h3 T)
  have h41 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w f I Fin.castSucc) (under h4 T)
  have h51 := of_eq (SyntaxTermImagePushSyntax.pushed_rename w R2 I A f B f F a G Fin.castSucc) (under h5 T)
  have h61 := of_eq (ForcingConditionRebind.mapped_rename w j t f B D Fin.castSucc) (under h6 T)
  have h71 := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w R3 I G D a f B f A C t K H Fin.castSucc) (under h7 T)
  have h81 := of_eq (SyntaxMixedImageCodeSyntax.encoded_rename w K A C f L Fin.castSucc) (under h8 T)
  have h91 := of_eq (SyntaxMixedImageCodeSyntax.encoded_rename w H f C f S Fin.castSucc) (under h9 T)
  have hk1 := of_eq (keepsHead_rename K z t Fin.castSucc) (under hk T)
  have hflow1 := of_eq (conditionFlow_rename w R3 I B C f t H j Fin.castSucc) (under hflow T)
  let v : Fin 12 → Fin (m+1) := Fin.cases z.castSucc (Fin.cases t.castSucc (Fin.cases F.castSucc (Fin.cases R2.castSucc (Fin.cases R3.castSucc (Fin.cases I.castSucc (Fin.cases G.castSucc (Fin.cases D.castSucc (Fin.cases K.castSucc (Fin.cases H.castSucc (Fin.cases L.castSucc (Fin.cases S.castSucc (fun i => Fin.elim0 i))))))))))))
  have hd : Derives Δ (data w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) v) := .conjI h01 (.conjI h11 (.conjI h21 (.conjI h31 (.conjI h41 (.conjI h51 (.conjI h61 (.conjI h71 (.conjI h81 (.conjI h91 (.conjI hT (.conjI hk1 hflow1)))))))))))
  have hc : Derives Δ (compiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)) := by
    apply HornBinderRules.intro_many 12 _ v
    exact of_eq (by simp only [body, data_rename, assign_old, assign_slot]) hd
  have ho : Derives Δ (existsCompiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, compiled_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hc
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage9 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2 R3 I G D K H L: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    (h3 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w B C R3))
    (h4 : Derives Γ (SyntaxIdentityMapSyntax.identityMap w f I))
    (h5 : Derives Γ (SyntaxTermImagePushSyntax.pushed w R2 I A f B f F a G))
    (h6 : Derives Γ (ForcingConditionRebind.mapped w j t f B D))
    (h7 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R3 I G D a f B f A C t K H))
    (h8 : Derives Γ (SyntaxMixedImageCodeSyntax.encoded w K A C f L))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxMixedImageCodeExistence.exists_code hZ w H f C f h.hw (.conjR (SyntaxMixedImageLiftFields.target_maps w R3 I G D a f B f A C t K H h7))
  let T := SyntaxMixedImageCodeSyntax.encoded w.castSucc H.castSucc f.castSucc C.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 Fin.castSucc) (under h2 T)
  have h31 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C R3 Fin.castSucc) (under h3 T)
  have h41 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w f I Fin.castSucc) (under h4 T)
  have h51 := of_eq (SyntaxTermImagePushSyntax.pushed_rename w R2 I A f B f F a G Fin.castSucc) (under h5 T)
  have h61 := of_eq (ForcingConditionRebind.mapped_rename w j t f B D Fin.castSucc) (under h6 T)
  have h71 := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w R3 I G D a f B f A C t K H Fin.castSucc) (under h7 T)
  have h81 := of_eq (SyntaxMixedImageCodeSyntax.encoded_rename w K A C f L Fin.castSucc) (under h8 T)
  have ho := assemble (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc F.castSucc R2.castSucc R3.castSucc I.castSucc G.castSucc D.castSucc K.castSucc H.castSucc L.castSucc (Fin.last m) (underInputs h T) h01 h11 h21 h31 h41 h51 h61 h71 h81 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage8 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2 R3 I G D K H: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    (h3 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w B C R3))
    (h4 : Derives Γ (SyntaxIdentityMapSyntax.identityMap w f I))
    (h5 : Derives Γ (SyntaxTermImagePushSyntax.pushed w R2 I A f B f F a G))
    (h6 : Derives Γ (ForcingConditionRebind.mapped w j t f B D))
    (h7 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R3 I G D a f B f A C t K H))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxMixedImageCodeExistence.exists_code hZ w K A C f h.hw (.conjL (SyntaxMixedImageLiftFields.target_maps w R3 I G D a f B f A C t K H h7))
  let T := SyntaxMixedImageCodeSyntax.encoded w.castSucc K.castSucc A.castSucc C.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 Fin.castSucc) (under h2 T)
  have h31 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C R3 Fin.castSucc) (under h3 T)
  have h41 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w f I Fin.castSucc) (under h4 T)
  have h51 := of_eq (SyntaxTermImagePushSyntax.pushed_rename w R2 I A f B f F a G Fin.castSucc) (under h5 T)
  have h61 := of_eq (ForcingConditionRebind.mapped_rename w j t f B D Fin.castSucc) (under h6 T)
  have h71 := of_eq (SyntaxMixedImageLiftSyntax.lifted_rename w R3 I G D a f B f A C t K H Fin.castSucc) (under h7 T)
  have ho := stage9 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc F.castSucc R2.castSucc R3.castSucc I.castSucc G.castSucc D.castSucc K.castSucc H.castSucc (Fin.last m) (underInputs h T) h01 h11 h21 h31 h41 h51 h61 h71 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage7 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2 R3 I G D: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    (h3 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w B C R3))
    (h4 : Derives Γ (SyntaxIdentityMapSyntax.identityMap w f I))
    (h5 : Derives Γ (SyntaxTermImagePushSyntax.pushed w R2 I A f B f F a G))
    (h6 : Derives Γ (ForcingConditionRebind.mapped w j t f B D))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxMixedImageLiftExistence.exists_pair hZ w R3 I G D a f B f A C t h.hw (.conjI (.conjL (.conjR (.conjR h5))) (.conjL h6)) (.conjI (.conjL (.conjR h3)) (.conjL h4)) (.conjR (.conjR h0)) h.hA
  let T := SyntaxMixedImageLiftSyntax.lifted (old 2 w) (old 2 R3) (old 2 I) (old 2 G) (old 2 D) (old 2 a) (old 2 f) (old 2 B) (old 2 f) (old 2 A) (old 2 C) (old 2 t) (slot 2 0) (slot 2 1)
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t (old 2)) (HornBinderRules.under_body 2 h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F (old 2)) (HornBinderRules.under_body 2 h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 (old 2)) (HornBinderRules.under_body 2 h2 T)
  have h31 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C R3 (old 2)) (HornBinderRules.under_body 2 h3 T)
  have h41 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w f I (old 2)) (HornBinderRules.under_body 2 h4 T)
  have h51 := of_eq (SyntaxTermImagePushSyntax.pushed_rename w R2 I A f B f F a G (old 2)) (HornBinderRules.under_body 2 h5 T)
  have h61 := of_eq (ForcingConditionRebind.mapped_rename w j t f B D (old 2)) (HornBinderRules.under_body 2 h6 T)
  have ho := stage8 (HornBinderRules.zf_body 2 hZ T) (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (old 2 N) (old 2 z) (old 2 t) (old 2 F) (old 2 R2) (old 2 R3) (old 2 I) (old 2 G) (old 2 D) (slot 2 0) (slot 2 1) (underInputs2 h T) h01 h11 h21 h31 h41 h51 h61 hT
  exact of_eq (existsCompiled_rename w a A B C f j N (old 2)).symm ho

private theorem stage6 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2 R3 I G: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    (h3 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w B C R3))
    (h4 : Derives Γ (SyntaxIdentityMapSyntax.identityMap w f I))
    (h5 : Derives Γ (SyntaxTermImagePushSyntax.pushed w R2 I A f B f F a G))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := ForcingConditionRebind.selected_map_exists hZ w j t f B h.hw (context_B hZ h) (SyntaxMixedImageHead.term_at_zero hZ w A B f z t h.hw (.conjL (context_A h)) (.conjR (context_A h)) h.hB (.conjL h0) (.conjL (.conjR h0)))
  let T := ForcingConditionRebind.mapped w.castSucc j.castSucc t.castSucc f.castSucc B.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 Fin.castSucc) (under h2 T)
  have h31 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C R3 Fin.castSucc) (under h3 T)
  have h41 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w f I Fin.castSucc) (under h4 T)
  have h51 := of_eq (SyntaxTermImagePushSyntax.pushed_rename w R2 I A f B f F a G Fin.castSucc) (under h5 T)
  have ho := stage7 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc F.castSucc R2.castSucc R3.castSucc I.castSucc G.castSucc (Fin.last m) (underInputs h T) h01 h11 h21 h31 h41 h51 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage5 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2 R3 I: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    (h3 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w B C R3))
    (h4 : Derives Γ (SyntaxIdentityMapSyntax.identityMap w f I))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxTermImagePushGraph.exists_push hZ w R2 I A f B f F a h.hw (SyntaxVariableTableUnique.shifted_type true w a A f F h1) (.conjI (.conjL (.conjR h2)) (.conjL h4))
  let T := SyntaxTermImagePushSyntax.pushed w.castSucc R2.castSucc I.castSucc A.castSucc f.castSucc B.castSucc f.castSucc F.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 Fin.castSucc) (under h2 T)
  have h31 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C R3 Fin.castSucc) (under h3 T)
  have h41 := of_eq (SyntaxIdentityMapSyntax.identityMap_rename w f I Fin.castSucc) (under h4 T)
  have ho := stage6 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc F.castSucc R2.castSucc R3.castSucc I.castSucc (Fin.last m) (underInputs h T) h01 h11 h21 h31 h41 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage4 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2 R3: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    (h3 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w B C R3))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxIdentityGraph.exists_map hZ w f (.conjR (context_A h))
  let T := SyntaxIdentityMapSyntax.identityMap w.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 Fin.castSucc) (under h2 T)
  have h31 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w B C R3 Fin.castSucc) (under h3 T)
  have ho := stage5 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc F.castSucc R2.castSucc R3.castSucc (Fin.last m) (underInputs h T) h01 h11 h21 h31 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage3 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F R2: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    (h2 : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w A B R2))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxFreeShiftGraph.exists_map hZ w B C h.hw (natural_B hZ h) h.hC
  let T := SyntaxFreeShiftSyntax.shiftMap w.castSucc B.castSucc C.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have h21 := of_eq (SyntaxFreeShiftSyntax.shiftMap_rename w A B R2 Fin.castSucc) (under h2 T)
  have ho := stage4 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc F.castSucc R2.castSucc (Fin.last m) (underInputs h T) h01 h11 h21 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage2 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t F: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    (h1 : Derives Γ (SyntaxVariableTableSyntax.shifted true w a A f F))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxFreeShiftGraph.exists_map hZ w A B h.hw (.conjL (context_A h)) h.hB
  let T := SyntaxFreeShiftSyntax.shiftMap w.castSucc A.castSucc B.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have h11 := of_eq (SyntaxVariableTableSyntax.shifted_rename true w a A f F Fin.castSucc) (under h1 T)
  have ho := stage3 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc F.castSucc (Fin.last m) (underInputs h T) h01 h11 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage1 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N z t: Fin m) (h : Inputs Γ w a A B C f N)
    (h0 : Derives Γ (SyntaxMixedImageHead.head w C f z t))
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxVariableTableExistence.shifted_exists hZ true w a A f h.hw (context_A h) h.ha h.hA
  let T := SyntaxVariableTableSyntax.shifted true w.castSucc a.castSucc A.castSucc f.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have h01 := of_eq (SyntaxMixedImageHead.head_rename w C f z t Fin.castSucc) (under h0 T)
  have ho := stage2 (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc z.castSucc t.castSucc (Fin.last m) (underInputs h T) h01 hT
  exact of_eq (existsCompiled_rename w a A B C f j N Fin.castSucc).symm ho

private theorem stage0 {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N: Fin m) (h : Inputs Γ w a A B C f N)
    : Derives Γ (existsCompiled w a A B C f j N) := by
  have he := SyntaxMixedImageHead.exists_head hZ w B C f h.hw (natural_B hZ h) (.conjR (context_A h)) h.hC
  let T := SyntaxMixedImageHead.head (old 2 w) (old 2 C) (old 2 f) (slot 2 0) (slot 2 1)
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ he
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho := stage1 (HornBinderRules.zf_body 2 hZ T) (old 2 w) (old 2 a) (old 2 A) (old 2 B) (old 2 C) (old 2 f) (old 2 j) (old 2 N) (slot 2 0) (slot 2 1) (underInputs2 h T)  hT
  exact of_eq (existsCompiled_rename w a A B C f j N (old 2)).symm ho

/-- All internal scopes and arbitrary designated free index are allowed. The
source has the name binder already; every environment/list/output is produced. -/
theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a A B C f j N : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w N A f)) : Derives Γ (existsCompiled w a A B C f j N) :=
  stage0 hZ w a A B C f j N ⟨hw,ha,hA,hB,hC,hn⟩

theorem compiled_type {m} {Γ : Context m} (w a A B C f j N Q : Fin m)
    (h : Derives Γ (compiled w a A B C f j N Q)) : Derives Γ (FormulaCodeSyntax.formulaCode w Q C f) := by
  let T := body w a A B C f j N Q
  let Δ := Context.add T (raisedContext 12 Γ)
  apply HornBinderRules.eliminate_many 12 T _ h
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w Q C f (old 12)).symm
    (SyntaxMixedFormulaJudgment.target_type (old 12 w) (slot 12 10) (slot 12 11) (old 12 A) (old 12 f) (old 12 C) (old 12 f) (old 12 N) (old 12 Q) (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hT))))))))))))


private theorem pushed_inputs_subst {m} {Γ : Context m} (w R I A f B F a G Rnew Inew Fnew: Fin m)
    (eR : Derives Γ (.equal R Rnew))
    (eI : Derives Γ (.equal I Inew))
    (eF : Derives Γ (.equal F Fnew))
    (h : Derives Γ (SyntaxTermImagePushSyntax.pushed w R I A f B f F a G)) : Derives Γ (SyntaxTermImagePushSyntax.pushed w Rnew Inew A f B f Fnew a G) := by
  let P0 := SyntaxTermImagePushSyntax.pushed w.castSucc (Fin.last m) I.castSucc A.castSucc f.castSucc B.castSucc f.castSucc F.castSucc a.castSucc G.castSucc
  have h1 : Derives Γ (SyntaxTermImagePushSyntax.pushed w Rnew I A f B f F a G) :=
    of_eq (by simp only [P0, Formula.instantiate, SyntaxTermImagePushSyntax.pushed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 eR (of_eq (by simp only [P0, Formula.instantiate, SyntaxTermImagePushSyntax.pushed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := SyntaxTermImagePushSyntax.pushed w.castSucc Rnew.castSucc (Fin.last m) A.castSucc f.castSucc B.castSucc f.castSucc F.castSucc a.castSucc G.castSucc
  have h2 : Derives Γ (SyntaxTermImagePushSyntax.pushed w Rnew Inew A f B f F a G) :=
    of_eq (by simp only [P1, Formula.instantiate, SyntaxTermImagePushSyntax.pushed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 eI (of_eq (by simp only [P1, Formula.instantiate, SyntaxTermImagePushSyntax.pushed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  let P2 := SyntaxTermImagePushSyntax.pushed w.castSucc Rnew.castSucc Inew.castSucc A.castSucc f.castSucc B.castSucc f.castSucc (Fin.last m) a.castSucc G.castSucc
  have h3 : Derives Γ (SyntaxTermImagePushSyntax.pushed w Rnew Inew A f B f Fnew a G) :=
    of_eq (by simp only [P2, Formula.instantiate, SyntaxTermImagePushSyntax.pushed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P2 eF (of_eq (by simp only [P2, Formula.instantiate, SyntaxTermImagePushSyntax.pushed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h2))
  exact h3

private theorem selected_term_subst {m} {Γ : Context m} (w j t f B D tnew: Fin m)
    (et : Derives Γ (.equal t tnew))
    (h : Derives Γ (ForcingConditionRebind.mapped w j t f B D)) : Derives Γ (ForcingConditionRebind.mapped w j tnew f B D) := by
  let P0 := ForcingConditionRebind.mapped w.castSucc j.castSucc (Fin.last m) f.castSucc B.castSucc D.castSucc
  have h1 : Derives Γ (ForcingConditionRebind.mapped w j tnew f B D) :=
    of_eq (by simp only [P0, Formula.instantiate, ForcingConditionRebind.mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 et (of_eq (by simp only [P0, Formula.instantiate, ForcingConditionRebind.mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  exact h1

private theorem lifted_inputs_subst {m} {Γ : Context m} (w R I G D a f B A C t K H Rnew Inew Gnew Dnew tnew: Fin m)
    (eR : Derives Γ (.equal R Rnew))
    (eI : Derives Γ (.equal I Inew))
    (eG : Derives Γ (.equal G Gnew))
    (eD : Derives Γ (.equal D Dnew))
    (et : Derives Γ (.equal t tnew))
    (h : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w R I G D a f B f A C t K H)) : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w Rnew Inew Gnew Dnew a f B f A C tnew K H) := by
  let P0 := SyntaxMixedImageLiftSyntax.lifted w.castSucc (Fin.last m) I.castSucc G.castSucc D.castSucc a.castSucc f.castSucc B.castSucc f.castSucc A.castSucc C.castSucc t.castSucc K.castSucc H.castSucc
  have h1 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w Rnew I G D a f B f A C t K H) :=
    of_eq (by simp only [P0, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 eR (of_eq (by simp only [P0, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := SyntaxMixedImageLiftSyntax.lifted w.castSucc Rnew.castSucc (Fin.last m) G.castSucc D.castSucc a.castSucc f.castSucc B.castSucc f.castSucc A.castSucc C.castSucc t.castSucc K.castSucc H.castSucc
  have h2 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w Rnew Inew G D a f B f A C t K H) :=
    of_eq (by simp only [P1, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 eI (of_eq (by simp only [P1, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  let P2 := SyntaxMixedImageLiftSyntax.lifted w.castSucc Rnew.castSucc Inew.castSucc (Fin.last m) D.castSucc a.castSucc f.castSucc B.castSucc f.castSucc A.castSucc C.castSucc t.castSucc K.castSucc H.castSucc
  have h3 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w Rnew Inew Gnew D a f B f A C t K H) :=
    of_eq (by simp only [P2, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P2 eG (of_eq (by simp only [P2, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h2))
  let P3 := SyntaxMixedImageLiftSyntax.lifted w.castSucc Rnew.castSucc Inew.castSucc Gnew.castSucc (Fin.last m) a.castSucc f.castSucc B.castSucc f.castSucc A.castSucc C.castSucc t.castSucc K.castSucc H.castSucc
  have h4 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w Rnew Inew Gnew Dnew a f B f A C t K H) :=
    of_eq (by simp only [P3, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P3 eD (of_eq (by simp only [P3, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h3))
  let P4 := SyntaxMixedImageLiftSyntax.lifted w.castSucc Rnew.castSucc Inew.castSucc Gnew.castSucc Dnew.castSucc a.castSucc f.castSucc B.castSucc f.castSucc A.castSucc C.castSucc (Fin.last m) K.castSucc H.castSucc
  have h5 : Derives Γ (SyntaxMixedImageLiftSyntax.lifted w Rnew Inew Gnew Dnew a f B f A C tnew K H) :=
    of_eq (by simp only [P4, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P4 et (of_eq (by simp only [P4, Formula.instantiate, SyntaxMixedImageLiftSyntax.lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h4))
  exact h5

private theorem mixed_lists_subst {m} {Γ : Context m} (w L S A f C N Q Lnew Snew: Fin m)
    (eL : Derives Γ (.equal L Lnew))
    (eS : Derives Γ (.equal S Snew))
    (h : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w L S A f C f N Q)) : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w Lnew Snew A f C f N Q) := by
  let P0 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc (Fin.last m) S.castSucc A.castSucc f.castSucc C.castSucc f.castSucc N.castSucc Q.castSucc
  have h1 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w Lnew S A f C f N Q) :=
    of_eq (by simp only [P0, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P0 eL (of_eq (by simp only [P0, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h))
  let P1 := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc Lnew.castSucc (Fin.last m) A.castSucc f.castSucc C.castSucc f.castSucc N.castSucc Q.castSucc
  have h2 : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w Lnew Snew A f C f N Q) :=
    of_eq (by simp only [P1, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P1 eS (of_eq (by simp only [P1, Formula.instantiate, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h1))
  exact h2

private theorem data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a A B C f j N Q V : Fin m) (xs ys : Fin 12 → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (data w a A B C f j N Q xs)) (hy : Derives Γ (data w a A B C f j N V ys)) : Derives Γ (.equal Q V) := by
  have hx0 := Derives.conjL hx
  have hy0 := Derives.conjL hy
  have hx1 := Derives.conjL (.conjR hx)
  have hy1 := Derives.conjL (.conjR hy)
  have hx2 := Derives.conjL (.conjR (.conjR hx))
  have hy2 := Derives.conjL (.conjR (.conjR hy))
  have hx3 := Derives.conjL (.conjR (.conjR (.conjR hx)))
  have hy3 := Derives.conjL (.conjR (.conjR (.conjR hy)))
  have hx4 := Derives.conjL (.conjR (.conjR (.conjR (.conjR hx))))
  have hy4 := Derives.conjL (.conjR (.conjR (.conjR (.conjR hy))))
  have hx5 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))
  have hy5 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))
  have hx6 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx))))))
  have hy6 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy))))))
  have hx7 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))))
  have hy7 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))))
  have hx8 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx))))))))
  have hy8 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy))))))))
  have hx9 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx)))))))))
  have hy9 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy)))))))))
  have hx10 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hx))))))))))
  have hy10 := Derives.conjL (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hy))))))))))

  have hz := OmegaUniversal.empty_unique (xs 0) (ys 0) (ZFContext.arithmetic hZ).base.extensionality (.conjL hx0) (.conjL hy0)
  have htc := AbstractVariableIndex.code_index_subst true w (xs 0) (ys 0) (xs 1) hz (.conjL (.conjR hx0))
  have ht := SyntaxVariables.unique hZ true w (ys 0) (xs 1) (ys 1) hw htc (.conjL (.conjR hy0))
  have hF := SyntaxVariableTableUnique.shifted_unique hZ true w a A f (xs 2) (ys 2) hx1 hy1
  have hR2 := SyntaxFreeShiftGraph.unique_map hZ w A B (xs 3) (ys 3) hx2 hy2
  have hR3 := SyntaxFreeShiftGraph.unique_map hZ w B C (xs 4) (ys 4) hx3 hy3
  have hI := SyntaxIdentityUnique.map_unique hZ w f (xs 5) (ys 5) hx4 hy4
  have hp := pushed_inputs_subst w (xs 3) (xs 5) A f B (xs 2) a (xs 6) (ys 3) (ys 5) (ys 2) hR2 hI hF hx5
  have hG := SyntaxTermImagePushGraph.unique hZ w (ys 3) (ys 5) A f B f (ys 2) a (xs 6) (ys 6) hp hy5
  have hd := selected_term_subst w j (xs 1) f B (xs 7) (ys 1) ht hx6
  have hD := ForcingConditionRebind.selected_map_unique hZ w j (ys 1) f B (xs 7) (ys 7) hd hy6
  have hl := lifted_inputs_subst w (xs 4) (xs 5) (xs 6) (xs 7) a f B A C (xs 1) (xs 8) (xs 9)
    (ys 4) (ys 5) (ys 6) (ys 7) (ys 1) hR3 hI hG hD ht hx7
  have hKH := SyntaxMixedImageLiftUnique.unique_pair hZ w (ys 4) (ys 5) (ys 6) (ys 7) a f B f A C (ys 1)
    (xs 8) (xs 9) (ys 8) (ys 9) hl hy7
  have hLe := SyntaxMixedImageCodeUnique.subst_graph w (xs 8) A C f (xs 10) (ys 8) (.conjL hKH) hx8
  have hL := SyntaxMixedImageCodeUnique.unique_code hZ w (ys 8) A C f (xs 10) (ys 10) hw hLe hy8
  have hSe := SyntaxMixedImageCodeUnique.subst_graph w (xs 9) f C f (xs 11) (ys 9) (.conjR hKH) hx9
  have hS := SyntaxMixedImageCodeUnique.unique_code hZ w (ys 9) f C f (xs 11) (ys 11) hw hSe hy9
  have hq := mixed_lists_subst w (xs 10) (xs 11) A f C N Q (ys 10) (ys 11) hL hS hx10
  exact SyntaxMixedFormulaOutputInduction.unique hZ w (ys 10) (ys 11) A f C f N Q V hw hq hy10

/-- Independent environment, index, image, prefix, list and substitution
executions determine a single output; no canonical witness is assumed. -/
theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a A B C f j N Q V : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled w a A B C f j N Q))
    (hv : Derives Γ (compiled w a A B C f j N V)) : Derives Γ (.equal Q V) := by
  let T := body w a A B C f j N Q
  let Δ := Context.add T (raisedContext 12 Γ)
  apply HornBinderRules.eliminate_many 12 T _ hq
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hv1 := of_eq (compiled_rename w a A B C f j N V (old 12)) (HornBinderRules.under_body 12 hv T)
  let U := body (old 12 w) (old 12 a) (old 12 A) (old 12 B) (old 12 C) (old 12 f) (old 12 j) (old 12 N) (old 12 V)
  let Ξ := Context.add U (raisedContext 12 Δ)
  apply HornBinderRules.eliminate_many 12 U _ hv1
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hw2 : Derives Ξ (omega (old 12 (old 12 w))) := of_eq (by simp only [omega_rename])
    (HornBinderRules.under_body 12 (HornBinderRules.under_body 12 hw T) U)
  have hx2 : Derives Ξ (data (old 12 (old 12 w)) (old 12 (old 12 a)) (old 12 (old 12 A)) (old 12 (old 12 B))
      (old 12 (old 12 C)) (old 12 (old 12 f)) (old 12 (old 12 j)) (old 12 (old 12 N)) (old 12 (old 12 Q)) (fun i => old 12 (slot 12 i))) :=
    of_eq (by simp only [T, body, data_rename]) (HornBinderRules.under_body 12 hT U)
  exact data_unique (HornBinderRules.zf_body 12 (HornBinderRules.zf_body 12 hZ T) U)
    (old 12 (old 12 w)) (old 12 (old 12 a)) (old 12 (old 12 A)) (old 12 (old 12 B)) (old 12 (old 12 C))
    (old 12 (old 12 f)) (old 12 (old 12 j)) (old 12 (old 12 N)) (old 12 (old 12 Q)) (old 12 (old 12 V))
    (fun i => old 12 (slot 12 i)) (slot 12) hw2 hx2 hU

def uniqueOutput {m} (w a A B C f j N Q : Fin m) : Formula m := .all
  ((compiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)).imp (.equal (Fin.last m) Q.castSucc))
private theorem uniqueOutput_rename {m l} (w a A B C f j N Q : Fin m) (r : Fin m → Fin l) :
    (uniqueOutput w a A B C f j N Q).rename r = uniqueOutput (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) (r Q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
private theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a A B C f j N Q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (compiled w a A B C f j N Q)) : Derives Γ (uniqueOutput w a A B C f j N Q) := by
  apply Derives.allI
  apply Derives.impI
  let T := compiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  exact unique (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) Q.castSucc
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) (.hyp (Or.inl rfl))
    (of_eq (compiled_rename w a A B C f j N Q Fin.castSucc) (under hq T))

def fiber {m} (w a A B C f j N : Fin m) : Formula m := .ex
  ((compiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)).conj
    ((FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) C.castSucc f.castSucc).conj
      (uniqueOutput w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m))))
private theorem fiber_rename {m l} (w a A B C f j N : Fin m) (r : Fin m → Fin l) :
    (fiber w a A B C f j N).rename r = fiber (r w) (r a) (r A) (r B) (r C) (r f) (r j) (r N) := by
  simp only [fiber, Formula.rename, compiled_rename, FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a A B C f j N : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w N A f)) : Derives Γ (fiber w a A B C f j N) := by
  let T := compiled w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (total hZ w a A B C f j N hw ha hA hB hC hn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ht := compiled_type w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m) hT
  have hu := unique_output (ZFContext.under hZ T) w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc (Fin.last m)
    (of_eq (omega_rename w Fin.castSucc) (under hw T)) hT
  have ho : Derives Δ (fiber w.castSucc a.castSucc A.castSucc B.castSucc C.castSucc f.castSucc j.castSucc N.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [T, Formula.instantiate, Formula.rename, compiled_rename,
      FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hT (.conjI ht hu))
  exact of_eq (fiber_rename w a A B C f j N Fin.castSucc).symm ho

def sentence {m} (w a A B C f j N : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((successor A a).imp ((successor B A).imp ((successor C B).imp ((FormulaCodeSyntax.formulaCode w N A f).imp (fiber w a A B C f j N))))))).close

theorem kernel_certificate {m} (w a A B C f j N : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (sentence w a A B C f j N)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact fiber_total (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) _) _) _) w a A B C f j N
    (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) (.hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def uniqueSentence {m} (w a A B C f j N Q V : Fin m) : Source.Sentence :=
  ((omega w).imp ((compiled w a A B C f j N Q).imp ((compiled w a A B C f j N V).imp (.equal Q V)))).close
theorem unique_kernel_certificate {m} (w a A B C f j N Q V : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (uniqueSentence w a A B C f j N Q V)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _)
    w a A B C f j N Q V (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingExistChildCode
