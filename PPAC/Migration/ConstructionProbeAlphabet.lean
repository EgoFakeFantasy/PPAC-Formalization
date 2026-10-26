/- Pinned ProbeWords.Path.exit, dvd_target_of_inCone, head_separation and alphabet.
The action and quotient are the already constructed source objects. -/
import PPAC.Migration.ConstructionProbeTarget
import PPAC.Migration.ConstructionBaseMonoid

namespace PPAC.Migration.ConstructionProbeAlphabet
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
open ConstructionProbePath
open ConstructionProbeLetters
open ConstructionProbeAction (ActionLaws projected_indices)
open ConstructionProbeTarget (TargetLaws)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ExitValue (mul K d c z : M.Carrier .set) : Prop :=
  ∃ t, PureKuratowski.PairMember M c t K ∧ Product mul t d z

def exitValue {m : Nat} (mul K d c z : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ c.succ 0))
    (ProjectSyntax.encode id (product mul.succ 0 d.succ z.succ)))

theorem exitValue_freeClosed {m : Nat} (mul K d c z : Fin m) : (exitValue mul K d c z).FreeClosed := by
  simp -implicitDefEqProofs [exitValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem exitValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (mul K d c z : Fin m) :
    Project.Formula.satisfies env (exitValue mul K d c z) ↔
      ExitValue (env.bound mul) (env.bound K) (env.bound d) (env.bound c) (env.bound z) := by
  simp only [exitValue,ExitValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,product_semantics (M := M)]
  rfl

def ExitGraph (mul K d E : M.Carrier .set) : Prop :=
  ∀ c z, PureKuratowski.PairMember M c z E ↔ ExitValue mul K d c z

theorem exists_exit (hM : FirstOrder.Theory.Models M nativeZF) {D mul e L K d : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hK : MapsTo L D K)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) :
    ∃ E, MapsTo L D E ∧ ExitGraph mul K d E := by
  let schema : Project.BinarySchema 3 :=
    { body := exitValue 2 3 4 1 0, freeClosed := exitValue_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases mul (Fin.cases K (fun _ => d)), free := fun _ => D }
  have he : ∀ c z, schema.denote env c z ↔ ExitValue mul K d c z :=
    fun c z => exitValue_semantics hM ((env.push c).push z) 2 3 4 1 0
  obtain ⟨E,hE,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := L) (target := D) (by
      intro c hc
      obtain ⟨t,ht,_⟩ := hK.1.2 c hc
      obtain ⟨z,_,hz⟩ := (hm.2.1 t (hK.2 c t ht)).1 d hd
      exact ⟨z,(he c z).mpr ⟨t,ht,hz⟩⟩) (by
      intro c _ z v hz hv
      obtain ⟨t,ht,hz⟩ := (he c z).mp hz
      obtain ⟨r,hr,hv⟩ := (he c v).mp hv
      have htr := ForcingConditionGraphs.function_unique hK.1 hr ht
      subst r
      exact (hm.2.1 t (hK.2 c t ht)).2.1 d z v hd hz hv) (by
      intro c z _ hz
      obtain ⟨t,ht,hz⟩ := (he c z).mp hz
      exact ConstructionProbeTransitions.product_closed hm (hK.2 c t ht) hd hz)
  refine ⟨E,(ForcingSupportSize.native_mapsTo hM L D E).mpr hE,fun c z => ?_⟩
  refine (hgraph c z).trans ⟨fun h => (he c z).mp h.2,fun h => ?_⟩
  have hcopy := h
  obtain ⟨t,ht,_⟩ := hcopy
  exact ⟨ForcingConditionGraphs.function_input hK.1 ht,(he c z).mpr h⟩

def InCone (L A b c : M.Carrier .set) : Prop :=
  ∃ t, (Project.FirstOrderSemantics.reduct M).mem t L ∧ Product A b t c

theorem dvd_target_of_inCone {D mul e L I A K projection T b c z : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hI : Representatives D L I) (hA : MapsTo I L A)
    (hK : MapsTo L D K) (hLaws : TargetLaws mul projection T A K)
    (hcone : InCone L A b c) (hz : PureKuratowski.PairMember M c z K) : Divides D mul b z := by
  obtain ⟨t,ht,hact⟩ := hcone
  obtain ⟨v,hv,_⟩ := hK.1.2 t ht
  have hb := (projected_indices hI hA hact).1
  obtain ⟨bv,_,hbv⟩ := (hm.2.1 b hb).1 v (hK.2 t v hv)
  have hcz := hLaws.2 b t c v bv hact hv hbv
  have he := ForcingConditionGraphs.function_unique hK.1 hcz hz
  exact ⟨v,hK.2 t v hv,he ▸ hbv⟩

theorem exit_act {D mul e L I A K projection T d E b c s z bz : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hI : Representatives D L I) (hA : MapsTo I L A)
    (hK : MapsTo L D K) (hLaws : TargetLaws mul projection T A K)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hE : ExitGraph mul K d E)
    (hact : Product A b c s) (hz : PureKuratowski.PairMember M c z E)
    (hbz : Product mul b z bz) : PureKuratowski.PairMember M s bz E := by
  obtain ⟨t,ht,htd⟩ := (hE c z).mp hz
  have hb := (projected_indices hI hA hact).1
  have htD := hK.2 c t ht
  obtain ⟨bt,_,hbt⟩ := (hm.2.1 b hb).1 t htD
  exact (hE s bz).mpr ⟨bt,hLaws.2 b c s t bt hact ht hbt,
    (hm.2.2 b t d bt z bz hb htD hd hbt htd).mpr hbz⟩

theorem head_separation {D mul e L I A K projection T d E c q : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hI : Representatives D L I) (hA : MapsTo I L A) (hK : MapsTo L D K)
    (hLaws : TargetLaws mul projection T A K)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hne : d ≠ e)
    (hE : ExitGraph mul K d E) (hq : PureKuratowski.PairMember M c q E) : ¬ InCone L A q c := by
  intro hcone
  obtain ⟨t,ht,htd⟩ := (hE c q).mp hq
  obtain ⟨v,hv,hqv⟩ := dvd_target_of_inCone hm hI hA hK hLaws hcone ht
  have htD := hK.2 c t ht
  obtain ⟨dv,hdvD,hdv⟩ := (hm.2.1 d hd).1 v hv
  have htdv := (hm.2.2 t d v q dv t htD hd hv htd hdv).mp hqv
  have hte : Product mul t e t := (hm.1.2 t htD t).2.mpr rfl
  have heq := (hm.2.1 t htD).2.2 dv e t hdvD hm.1.1 htdv hte
  exact hne (hc d v hd hv (heq ▸ hdv)).1

def ExitLaws (mul L A E : M.Carrier .set) : Prop :=
  (∀ b c s z bz, Product A b c s → PureKuratowski.PairMember M c z E →
    Product mul b z bz → PureKuratowski.PairMember M s bz E) ∧
  (∀ c q, (Project.FirstOrderSemantics.reduct M).mem c L →
    PureKuratowski.PairMember M c q E → ¬ InCone L A q c)

def Alphabet (D mul e L I A E : M.Carrier .set) : Prop :=
  Representatives D L I ∧ MapsTo I L A ∧ ActionLaws mul e L A ∧ MapsTo L D E ∧ ExitLaws mul L A E

theorem alphabet_laws {D mul e L I A K projection T d E : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hI : Representatives D L I) (hA : MapsTo I L A) (ha : ActionLaws mul e L A)
    (hK : MapsTo L D K) (hLaws : TargetLaws mul projection T A K)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) (hne : d ≠ e)
    (hEm : MapsTo L D E) (hE : ExitGraph mul K d E) : Alphabet D mul e L I A E := by
  exact ⟨hI,hA,ha,hEm,
    fun _ _ _ _ _ hact hz hbz => exit_act hm hI hA hK hLaws hd hE hact hz hbz,
    fun _ _ _ hq => head_separation hm hc hI hA hK hLaws hd hne hE hq⟩

def exitGraph {m : Nat} (mul K d E : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ 1 0)) (exitValue
    mul.succ.succ K.succ.succ d.succ.succ 1 0))))

theorem exitGraph_freeClosed {m : Nat} (mul K d E : Fin m) : (exitGraph mul K d E).FreeClosed := by
  simp -implicitDefEqProofs [exitGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,exitValue_freeClosed]

theorem exitGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (mul K d E : Fin m) :
    Project.Formula.satisfies env (exitGraph mul K d E) ↔
      ExitGraph (env.bound mul) (env.bound K) (env.bound d) (env.bound E) := by
  simp only [exitGraph,
    ExitGraph,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    exitValue_semantics hM]
  rfl

def inCone {m : Nat} (L A b c : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (.mem (.bound 0) (.bound L.succ)) (ProjectSyntax.encode id (product A.succ b.succ 0
    c.succ))))

theorem inCone_freeClosed {m : Nat} (L A b c : Fin m) : (inCone L A b c).FreeClosed := by
  simp -implicitDefEqProofs [inCone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem inCone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (L A b c : Fin m) :
    Project.Formula.satisfies env (inCone L A b c) ↔
      InCone (env.bound L) (env.bound A) (env.bound b) (env.bound c) := by
  simp only [inCone,
    InCone,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    product_semantics (M := M)]
  rfl

def exitLaws {m : Nat} (mul L A E : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (product
    A.succ.succ.succ.succ.succ 4 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    E.succ.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (product mul.succ.succ.succ.succ.succ 4 1
    0)) (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ.succ.succ.succ 2 0)))))))))) (.forallE
    (.forallE (.imp (.mem (.bound 1) (.bound L.succ.succ)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge E.succ.succ 1 0)) (.neg (inCone L.succ.succ A.succ.succ 0 1)))))))

theorem exitLaws_freeClosed {m : Nat} (mul L A E : Fin m) : (exitLaws mul L A E).FreeClosed := by
  simp -implicitDefEqProofs [exitLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,inCone_freeClosed]

theorem exitLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (mul L A E : Fin m) :
    Project.Formula.satisfies env (exitLaws mul L A E) ↔
      ExitLaws (env.bound mul) (env.bound L) (env.bound A) (env.bound E) := by
  simp only [exitLaws,
    ExitLaws,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    product_semantics (M := M),
    inCone_semantics hM]
  rfl

def alphabet {m : Nat} (D mul e L I A E : Fin m) : Project.Formula 1 m :=
  (.conj (representatives D L I) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo A I L)) (.conj
    (ConstructionProbeAction.actionLaws mul e L A) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo E
    L D)) (exitLaws mul L A E)))))

theorem alphabet_freeClosed {m : Nat} (D mul e L I A E : Fin m) : (alphabet D mul e L I A E).FreeClosed := by
  simp -implicitDefEqProofs [alphabet,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    exitLaws_freeClosed,representatives_freeClosed,
    ConstructionProbeAction.actionLaws_freeClosed]

theorem alphabet_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e L I A E : Fin m) :
    Project.Formula.satisfies env (alphabet D mul e L I A E) ↔
      Alphabet (env.bound D) (env.bound mul) (env.bound e) (env.bound L) (env.bound I) (env.bound A) (env.bound E) := by
  simp only [alphabet,
    Alphabet,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeAction.actionLaws_semantics hM,
    exitLaws_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 8 (.imp (Project.Formula.isOmega (.bound 0)) (.imp (.forallE (.neg (.mem (.bound
    0) (.bound 5)))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 8) 2 3))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 8) 2 3)) (.imp (.mem (.bound 7) (.bound
    1)) (.imp (.neg (Project.Formula.extensionalEq (.bound 7) (.bound 3))) (.imp (path (0 : Fin 8) 1 2 3 4 5 6)
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (factorTable (9 : Fin 17) 10 11 15 8) (.conj (terminalTable (9 : Fin 17) 10 11 15 14 7) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 17) 9 10)) (.conj (representatives (9 : Fin 17)
    10 6) (.conj (letters (9 : Fin 17) 10 11 8 6 5) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (4 : Fin 17) 6 5)) (.conj (projectionGraph (9 : Fin 17) 10 11 8 6 4) (.conj (equalityLaw (9 : Fin 17) 10 11
    8 4) (.conj (ConstructionProbeAction.actionTable (10 : Fin 17) 11 4 2) (.conj
    (ConstructionProbeAction.letterActionLaw (10 : Fin 17) 11 4 2) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (1 : Fin 17) 5 10)) (.conj (ConstructionProbeTarget.targetGraph (10 : Fin 17) 11
    4 7 1) (.conj (ConstructionProbeTarget.targetLaws (11 : Fin 17) 4 7 2 1) (.conj (exitGraph (11 : Fin 17) 1
    16 0) (alphabet (10 : Fin 17) 11 12 5 3 2 0))))))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    path_freeClosed,factorTable_freeClosed,terminalTable_freeClosed,representatives_freeClosed,letters_freeClosed,
    projectionGraph_freeClosed,equalityLaw_freeClosed,ConstructionProbeAction.actionTable_freeClosed,
    ConstructionProbeAction.letterActionLaw_freeClosed,ConstructionProbeTarget.targetGraph_freeClosed,
    ConstructionProbeTarget.targetLaws_freeClosed,exitGraph_freeClosed,alphabet_freeClosed,
    Project.Formula.extensionalEq]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    path_semantics hM,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    factorTable_semantics hM,terminalTable_semantics hM,representatives_semantics hM,letters_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),projectionGraph_semantics hM,equalityLaw_semantics hM,
    ConstructionProbeAction.actionTable_semantics hM,ConstructionProbeAction.letterActionLaw_semantics hM,
    ConstructionProbeTarget.targetGraph_semantics hM,ConstructionProbeTarget.targetLaws_semantics hM,
    exitGraph_semantics hM,alphabet_semantics hM]
  intro hw hz hm hc hd hne hp
  obtain ⟨pairs,hpairs⟩ := exists_ordered_pairs hM (bound 0)
  obtain ⟨F,_,hF⟩ := exists_factor_table hM hm hp hpairs
  obtain ⟨T,hTm,hT⟩ := exists_terminal_table hM hm hp
  have hTable := table_laws hM hw hz hm hp hF hT
  have hLaws := ConstructionProbeTransitions.meets_laws hM hw hm hp hF hTable
  obtain ⟨C,hC⟩ := exists_representatives hM (bound 0) (bound 1)
  obtain ⟨L,hL⟩ := exists_letters hM (bound 0) (bound 1) (bound 2) F C
  obtain ⟨projection,hp,hProjection⟩ := exists_projection hM hL
  have hE := equality_law hM hC hLaws hProjection
  obtain ⟨I,A,hI,hA,hAction⟩ := ConstructionProbeAction.exists_action hM hm hF hC hL hp hProjection hE
  obtain ⟨K,hK,hTarget⟩ := ConstructionProbeTarget.exists_target hM hm hF hC hL hp hProjection hE hTm hTable
  have hKLaws := ConstructionProbeTarget.target_laws hm hF hC hp hE hTm hTable hAction hTarget
  obtain ⟨E,hEm,hExit⟩ := exists_exit hM hm hK hd
  exact ⟨F,T,C,L,projection,I,A,K,E,hF,hT,hTm,hC,hL,hp,hProjection,hE,hAction,
    ConstructionProbeAction.letter_action_law hM hm hF hC hp hE hAction,hK,hTarget,hKLaws,hExit,
    alphabet_laws hm hc hI hA
      (ConstructionProbeAction.action_laws hM hm hF hC hL hp hProjection hE hAction)
      hK hKLaws hd hne hEm hExit⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeAlphabet
