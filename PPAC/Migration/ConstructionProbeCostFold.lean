/- The actual pinned Word.cost graph. Existing Raw evalHom folds internal
(word,cost) states; formula-indexed Raw induction verifies the word component.
The total-extension default is therefore absent from the source equations. -/
import PPAC.Migration.ConstructionProbeCostOperation

namespace PPAC.Migration.ConstructionProbeCostFold
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionProbeRaw
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeOldEmbedding (OldGraph)
open ConstructionProbeCostOperation (Update Initial)
open ConstructionProbeHomEvaluation (Eval Prepend)
open ConstructionProbeHomEvaluationSyntax (LiftGraph)
open ConstructionProbeLetters (Representatives)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem prepend_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S W Q R Cap V default T N G Id s t q v z out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hT : Representatives W R T)
    (hSN : Subset S N) (hTN : Subset T N) (hi : ForcingConditionGraphs.IdentityGraph S Id)
    (hg : ConstructionProbeCostOperation.Graph hM w D S W Q R Cap V default N G)
    (ht : (Project.FirstOrderSemantics.reduct M).mem t W) (hv : (Project.FirstOrderSemantics.reduct M).mem v R)
    (hz : PureKuratowski.Code M z t v) (hCons : Cons w D S s t q)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) :
    Prepend Id G s z out ↔ ∃ c, Update hM w Q Cap V q s v c ∧ PureKuratowski.Code M out q c := by
  constructor
  · rintro ⟨a,ha,hprod⟩
    have he := ((hi s a).mp ha).2
    subst a
    rcases ((hg s z out).mp hprod).2.2 with ⟨t',v',q',c,_,_,hz',hcons',_,hu,hout⟩ | ⟨hn,_⟩
    · obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
      have he := cons_unique hM hw hCons hcons'
      subst q'
      exact ⟨c,hu,hout⟩
    · exact (hn ⟨t,v,q,ht,hv,hz,hCons,hq⟩).elim
  · rintro ⟨c,hu,hout⟩
    have hs := ConstructionProbeRawAction.cons_letter hCons
    exact ⟨s,(hi s s).mpr ⟨hs,rfl⟩,(hg s z out).mpr
      ⟨hSN s hs,hTN z ((hT z).mpr ⟨t,v,ht,hv,hz⟩),Or.inl ⟨t,v,q,c,ht,hv,hz,hCons,hq,hu,hout⟩⟩⟩

def correct {m : Nat} (W L q : Fin m) : Project.Formula 1 m :=
  .imp (.mem (.bound q) (.bound W)) (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge L.succ q.succ 0))
    (.existsE (PureKuratowskiProject.code (.bound 1) (.bound q.succ.succ) (.bound 0)))))

theorem correct_freeClosed {m : Nat} (W L q : Fin m) : (correct W L q).FreeClosed := by
  simp -implicitDefEqProofs [correct,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem correct_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W L q : Fin m) :
    Project.Formula.satisfies env (correct W L q) ↔
      ((Project.FirstOrderSemantics.reduct M).mem (env.bound q) (env.bound W) →
        ∀ z, PureKuratowski.PairMember M (env.bound q) z (env.bound L) →
          ∃ c, PureKuratowski.Code M z (env.bound q) c) := by
  simp only [correct,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.code_correct hM]
  rfl

/-- The actual word component equals the input word, at every internal length. -/
theorem state_correct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Cap V default T N J G Id O C F LS : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hO : MapsTo D W O) (hOld : OldGraph zero D O)
    (hT : Representatives W R T) (hSN : Subset S N) (hTN : Subset T N)
    (hF : MapsTo D T F) (hG : MapsTo J T G)
    (hInit : ∀ x z, PureKuratowski.PairMember M x z F ↔ (Project.FirstOrderSemantics.reduct M).mem x D ∧ Initial O C x z)
    (hi : ForcingConditionGraphs.IdentityGraph S Id)
    (hg : ConstructionProbeCostOperation.Graph hM w D S W Q R Cap V default N G)
    (hl : LiftGraph hM w D S N G F Id W LS) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W →
      ∀ z, PureKuratowski.PairMember M q z LS → ∃ c, PureKuratowski.Code M z q c := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases W (fun _ => LS), free := fun _ => w }
  let p : Project.UnarySchema 2 := { body := correct 1 2 0, freeClosed := correct_freeClosed _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ((Project.FirstOrderSemantics.reduct M).mem q W → ∀ z, PureKuratowski.PairMember M q z LS →
        ∃ c, PureKuratowski.Code M z q c) := correct_semantics hM (env.push q) 1 2 0
  have hWords := ConstructionProbeWord.word_laws hM hw hz hzw hW
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOldQ
    apply (he q).mpr
    intro _ z hqz
    have hxz := ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOldQ ((hl q z).mp hqz).2
    obtain ⟨_,q',c,hxq',hxc,hzc⟩ := (hInit x z).mp hxz
    have hqq := ForcingConditionGraphs.function_unique hO.1 ((hOld x q).mpr hOldQ) hxq'
    subst q'
    exact ⟨c,hzc⟩) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro hq z hqz
    have ht := ((hWords.2.1 s t q hCons).mp hq).1
    obtain ⟨zin,hEval,hprep⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons ((hl q z).mp hqz).2
    obtain ⟨v,hzCode⟩ := (he t).mp ih ht zin ((hl t zin).mpr ⟨ht,hEval⟩)
    have hzT := ConstructionProbeHeightFold.eval_range hM hF hG hEval
    obtain ⟨t',v',ht',hv,hzCode'⟩ := (hT zin).mp hzT
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hzCode hzCode'
    obtain ⟨c,_,hzc⟩ := (prepend_iff hM hw hT hSN hTN hi hg ht hv hzCode hCons hq).mp hprep
    exact ⟨c,hzc⟩)
  intro q hq
  exact (he q).mp (hAll q (ConstructionProbeWord.word_raw hW hq)) hq

def Projected (LS q c : M.Carrier .set) : Prop :=
  ∃ z, PureKuratowski.PairMember M q z LS ∧ PureKuratowski.Code M z q c

def projected {m : Nat} (LS q c : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge LS.succ q.succ 0))
    (PureKuratowskiProject.code (.bound 0) (.bound q.succ) (.bound c.succ)))

theorem projected_freeClosed {m : Nat} (LS q c : Fin m) : (projected LS q c).FreeClosed := by
  simp -implicitDefEqProofs [projected,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem projected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (LS q c : Fin m) :
    Project.Formula.satisfies env (projected LS q c) ↔ Projected (env.bound LS) (env.bound q) (env.bound c) := by
  simp only [projected,Projected,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.code_correct hM,Project.Term.eval_bound]
  rfl

def Graph (W LS C : M.Carrier .set) : Prop := ∀ q c, PureKuratowski.PairMember M q c C ↔
  (Project.FirstOrderSemantics.reduct M).mem q W ∧ Projected LS q c

theorem exists_projection (hM : FirstOrder.Theory.Models M nativeZF) {W R T LS : M.Carrier .set}
    (hT : Representatives W R T) (hLS : MapsTo W T LS)
    (hCorrect : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W →
      ∀ z, PureKuratowski.PairMember M q z LS → ∃ c, PureKuratowski.Code M z q c) :
    ∃ C, MapsTo W R C ∧ Graph W LS C := by
  let schema : Project.BinarySchema 1 := { body := projected 2 1 0, freeClosed := projected_freeClosed _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => LS, free := fun _ => W }
  have he (q c : M.Carrier .set) : schema.denote env q c ↔ Projected LS q c :=
    projected_semantics hM ((env.push q).push c) 2 1 0
  obtain ⟨C,hC,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := W) (target := R) (by
      intro q hq
      obtain ⟨z,hz,_⟩ := hLS.1.2 q hq
      obtain ⟨c,hc⟩ := hCorrect q hq z hz
      exact ⟨c,(he q c).mpr ⟨z,hz,hc⟩⟩) (by
      intro q _ c d hc hd
      obtain ⟨z,hz,hzc⟩ := (he q c).mp hc
      obtain ⟨z',hz',hzd⟩ := (he q d).mp hd
      have he := ForcingConditionGraphs.function_unique hLS.1 hz hz'
      subst z'
      exact (PureKuratowski.code_injective hzc hzd).2) (by
      intro q c _ hc
      obtain ⟨z,hz,hzc⟩ := (he q c).mp hc
      obtain ⟨q',c',_,hc',hzc'⟩ := (hT z).mp (hLS.2 q z hz)
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hzc hzc'
      exact hc')
  exact ⟨C,(ForcingSupportSize.native_mapsTo hM W R C).mpr hC,
    fun q c => (hg q c).trans (and_congr_right (fun _ => he q c))⟩

def Laws (hM : FirstOrder.Theory.Models M nativeZF) (w D S zero W Q C V Cap LC : M.Carrier .set) : Prop :=
  (∀ x q c, Old zero D x q → (PureKuratowski.PairMember M q c LC ↔ PureKuratowski.PairMember M x c C)) ∧
  (∀ s t q c, Cons w D S s t q → (Project.FirstOrderSemantics.reduct M).mem q W →
    (PureKuratowski.PairMember M q c LC ↔ ∃ v, PureKuratowski.PairMember M t v LC ∧ Update hM w Q Cap V q s v c))

theorem cost_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R Cap V default T N J G Id O C F LS LC : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hO : MapsTo D W O) (hOld : OldGraph zero D O)
    (hT : Representatives W R T) (hSN : Subset S N) (hTN : Subset T N)
    (hJ : Representatives N N J) (hGN : MapsTo J N G) (hFN : MapsTo D N F) (hId : MapsTo S N Id)
    (hi : ForcingConditionGraphs.IdentityGraph S Id)
    (hg : ConstructionProbeCostOperation.Graph hM w D S W Q R Cap V default N G)
    (hInit : ∀ x z, PureKuratowski.PairMember M x z F ↔ (Project.FirstOrderSemantics.reduct M).mem x D ∧ Initial O C x z)
    (hl : LiftGraph hM w D S N G F Id W LS) (hp : Graph W LS LC) (hLC : MapsTo W R LC)
    (hCorrect : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W →
      ∀ z, PureKuratowski.PairMember M q z LS → ∃ c, PureKuratowski.Code M z q c) :
    Laws hM w D S zero W Q C V Cap LC := by
  have hWords := ConstructionProbeWord.word_laws hM hw hz hzw hW
  constructor
  · intro x q c hOldQ
    constructor
    · intro hqc
      obtain ⟨_,z,hqz,hzc⟩ := (hp q c).mp hqc
      have hxz := ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOldQ ((hl q z).mp hqz).2
      obtain ⟨_,q',c',hxq,hxc,hzc'⟩ := (hInit x z).mp hxz
      have he := ForcingConditionGraphs.function_unique hO.1 ((hOld x q).mpr hOldQ) hxq
      subst q'
      exact (PureKuratowski.code_injective hzc hzc').2.symm ▸ hxc
    · intro hxc
      have hq := hWords.1 x q hOldQ
      obtain ⟨z,hzc⟩ := KuratowskiZF.exists_code hM q c
      have hxz := (hInit x z).mpr ⟨hOldQ.1,q,c,(hOld x q).mpr hOldQ,hxc,hzc⟩
      have hEval := (ConstructionProbeHomEvaluation.eval_old_iff hM hw hz hzw hJ hGN hFN hId hOldQ).mpr hxz
      exact (hp q c).mpr ⟨hq,z,(hl q z).mpr ⟨hq,hEval⟩,hzc⟩
  · intro s t q c hCons hq
    have ht := ((hWords.2.1 s t q hCons).mp hq).1
    constructor
    · intro hqc
      obtain ⟨_,z,hqz,hzc⟩ := (hp q c).mp hqc
      obtain ⟨zin,hTail,hprep⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons ((hl q z).mp hqz).2
      have htz := (hl t zin).mpr ⟨ht,hTail⟩
      obtain ⟨v,hzin⟩ := hCorrect t ht zin htz
      have htv := (hp t v).mpr ⟨ht,zin,htz,hzin⟩
      obtain ⟨c',hup,hzc'⟩ := (prepend_iff hM hw hT hSN hTN hi hg ht (hLC.2 t v htv) hzin hCons hq).mp hprep
      exact ⟨v,htv,(PureKuratowski.code_injective hzc hzc').2.symm ▸ hup⟩
    · rintro ⟨v,htv,hup⟩
      obtain ⟨_,zin,htz,hzin⟩ := (hp t v).mp htv
      have hTail := ((hl t zin).mp htz).2
      obtain ⟨z,hzc⟩ := KuratowskiZF.exists_code hM q c
      have hprep := (prepend_iff hM hw hT hSN hTN hi hg ht (hLC.2 t v htv) hzin hCons hq).mpr ⟨c,hup,hzc⟩
      have hEval := (ConstructionProbeHomEvaluation.eval_cons_iff hM hw hJ hGN hFN hId hCons).mpr ⟨zin,hTail,hprep⟩
      exact (hp q c).mpr ⟨hq,z,(hl q z).mpr ⟨hq,hEval⟩,hzc⟩

/-- Actual Word cost, constructed by the existing internal Raw fold and
native state projection. No cost graph or correct-state oracle is assumed. -/
theorem exists_cost (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R O C V Cap e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hO : MapsTo D W O) (hOld : OldGraph zero D O) (hC : MapsTo D R C)
    (hV : MapsTo S R V) (hCap : MapsTo W R Cap)
    (hW : WordCarrier w D S mul A b W) (heD : (Project.FirstOrderSemantics.reduct M).mem e D) :
    ∃ LC, MapsTo W R LC ∧ Laws hM w D S zero W Q C V Cap LC := by
  obtain ⟨T,hT⟩ := ConstructionProbeLetters.exists_representatives hM W R
  obtain ⟨F,hF,hInit⟩ := ConstructionProbeCostOperation.exists_initial hM hO hC hT
  obtain ⟨default,hDefault,_⟩ := hF.1.2 e heD
  have hdT := hF.2 e default hDefault
  obtain ⟨N,hN⟩ := KP.exists_unionOfTwo (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) S T
  have hSN : Subset S N := fun s hs => (hN s).mpr (Or.inl hs)
  have hTN : Subset T N := fun t ht => (hN t).mpr (Or.inr ht)
  obtain ⟨J,G,hJ,hG,hg⟩ := ConstructionProbeCostOperation.exists_operation hM hw hQ hR hCap hV hT hdT N
  have hGN : MapsTo J N G := ⟨hG.1,fun x y hy => hTN y (hG.2 x y hy)⟩
  have hFN : MapsTo D N F := ⟨hF.1,fun x y hy => hTN y (hF.2 x y hy)⟩
  obtain ⟨Id,hIdPerm,hi⟩ := ForcingConditionGraphs.exists_identity hM S
  have hId : MapsTo S N Id := ⟨hIdPerm.1.1,fun x y hy => hSN y (hIdPerm.1.2 x y hy)⟩
  obtain ⟨LS,hLS,hl⟩ := ConstructionProbeHomEvaluationSyntax.exists_lift_graph hM hw hJ hGN hFN hId hW
  have hLST : MapsTo W T LS := ⟨hLS.1,fun q z hqz => ConstructionProbeHeightFold.eval_range hM hF hG ((hl q z).mp hqz).2⟩
  have hCorrect := state_correct hM hw hz hzw hW hO hOld hT hSN hTN hF hG hInit hi hg hl
  obtain ⟨LC,hLC,hp⟩ := exists_projection hM hT hLST hCorrect
  exact ⟨LC,hLC,cost_laws hM hw hz hzw hW hO hOld hT hSN hTN hJ hGN hFN hId hi hg hInit hl hp hLC hCorrect⟩

theorem cost_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R C V Cap LC KC : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hC : MapsTo D R C) (hV : MapsTo S R V) (hCap : MapsTo W R Cap)
    (hLC : MapsTo W R LC) (hKC : MapsTo W R KC)
    (hl : Laws hM w D S zero W Q C V Cap LC) (hk : Laws hM w D S zero W Q C V Cap KC) : LC = KC := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases W (Fin.cases LC (fun _ => KC)), free := fun _ => w }
  let p : Project.UnarySchema 3 := {
    body := ConstructionProbeHomExt.agreement 1 2 3 0
    freeClosed := ConstructionProbeHomExt.agreement_freeClosed _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ((Project.FirstOrderSemantics.reduct M).mem q W → ConstructionProbeHomExt.AgreeAt q LC KC) :=
    ConstructionProbeHomExt.agreement_semantics hM (env.push q) 1 2 3 0
  have hWords := ConstructionProbeWord.word_laws hM hw hz hzw hW
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOldQ
    apply (he q).mpr
    intro _ c d hc hd
    exact ForcingConditionGraphs.function_unique hC.1 ((hl.1 x q c hOldQ).mp hc) ((hk.1 x q d hOldQ).mp hd)) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro hq c d hc hd
    have ht := ((hWords.2.1 s t q hCons).mp hq).1
    obtain ⟨v,hv,hup⟩ := (hl.2 s t q c hCons hq).mp hc
    obtain ⟨v',hv',hup'⟩ := (hk.2 s t q d hCons hq).mp hd
    have he := (he t).mp ih ht v v' hv hv'
    subst v'
    exact ConstructionProbeCostOperation.update_unique hM hCap hV hup hup')
  have hAgree := fun q hq => (he q).mp (hAll q (ConstructionProbeWord.word_raw hW hq)) hq
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM W R LC).mp hLC).1.1
    ((ForcingSupportSize.native_mapsTo hM W R KC).mp hKC).1.1
  intro q c
  constructor
  · intro hc
    have hq := ForcingConditionGraphs.function_input hLC.1 hc
    obtain ⟨d,hd,_⟩ := hKC.1.2 q hq
    exact (hAgree q hq c d hc hd).symm ▸ hd
  · intro hc
    have hq := ForcingConditionGraphs.function_input hKC.1 hc
    obtain ⟨d,hd,_⟩ := hLC.1.2 q hq
    exact (hAgree q hq d c hd hc) ▸ hd

/-- The source min cap argument gives the non-strict cost bound without
assuming a multiplier upper bound or rebuilding a real-field library. -/
theorem update_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R W S Cap V unit q s v c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hCap : MapsTo W R Cap) (hV : MapsTo S R V)
    (hCapB : ConstructionProbeGateCap.Bounds unit Cap)
    (hVP : ∀ s d, PureKuratowski.PairMember M s d V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d)
    (hv : (Project.FirstOrderSemantics.reduct M).mem v R) (hvn : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p v)
    (hu : Update hM w Q Cap V q s v c) :
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧ Subset c unit := by
  obtain ⟨d,p,cap,hd,hprod,hcap,hmin⟩ := hu
  have hD := (hR d).mp (hV.2 s d hd)
  have hV := (hR v).mp hv
  have hP := ConstructionCutProduct.value_cut hM hw hQ hD hV hprod
  have hPN := ConstructionCutProduct.value_nonempty hM hw hQ hD hV hprod (hVP s d hd) hvn
  have hB := hCapB q cap hcap
  have hCN := ConstructionCutMinimum.value_nonempty hM hw hQ hP ((hR cap).mp (hCap.2 q cap hcap)) hmin hPN hB.1
  exact ⟨hCN,fun x hx => hB.2 x ((ConstructionCutMinimum.value_bounds hmin).2 x hx)⟩

def boundAt {m : Nat} (unit LC q : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge LC.succ q.succ 0))
    (.conj (.existsE (.mem (.bound 0) (.bound 1)))
      (Project.Formula.subset (.bound 0) (.bound unit.succ))))

theorem boundAt_freeClosed {m : Nat} (unit LC q : Fin m) : (boundAt unit LC q).FreeClosed := by
  simp -implicitDefEqProofs [boundAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem boundAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (unit LC q : Fin m) :
    Project.Formula.satisfies env (boundAt unit LC q) ↔
      ∀ c, PureKuratowski.PairMember M (env.bound q) c (env.bound LC) →
        (∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧ Subset c (env.bound unit) := by
  simp only [boundAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem cost_bounds (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R C V Cap LC unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hW : WordCarrier w D S mul A b W) (hLC : MapsTo W R LC) (hV : MapsTo S R V) (hCap : MapsTo W R Cap)
    (hCB : ConstructionProbeGateCap.Bounds unit C) (hCapB : ConstructionProbeGateCap.Bounds unit Cap)
    (hVP : ∀ s d, PureKuratowski.PairMember M s d V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d)
    (hl : Laws hM w D S zero W Q C V Cap LC) : ConstructionProbeGateCap.Bounds unit LC := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases unit (fun _ => LC), free := fun _ => w }
  let p : Project.UnarySchema 2 := { body := boundAt 1 2 0, freeClosed := boundAt_freeClosed _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔ ∀ c, PureKuratowski.PairMember M q c LC →
      (∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧ Subset c unit := boundAt_semantics hM (env.push q) 1 2 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOldQ
    exact (he q).mpr (fun c hc => hCB x c ((hl.1 x q c hOldQ).mp hc))) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro c hc
    have hq := ForcingConditionGraphs.function_input hLC.1 hc
    obtain ⟨v,hv,hup⟩ := (hl.2 s t q c hCons hq).mp hc
    exact update_bounds hM hw hQ hR hCap hV hCapB hVP (hLC.2 t v hv) ((he t).mp ih v hv).1 hup)
  intro q c hc
  have hq := ForcingConditionGraphs.function_input hLC.1 hc
  exact (he q).mp (hAll q (ConstructionProbeWord.word_raw hW hq)) c hc

/-- Assemble the actual source gateCap and cost on the same Word carrier.
The only bound inputs are the original old cost bound and scale positivity. -/
theorem exists_bounded_cost (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R O C V e unit G : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hCon : ForcingDiagramPoset.Conical D mul e)
    (hW : WordCarrier w D S mul A b W) (hO : MapsTo D W O) (hOld : OldGraph zero D O)
    (hC : MapsTo D R C) (hV : MapsTo S R V)
    (hu : (Project.FirstOrderSemantics.reduct M).mem unit R)
    (hun : ∃ p, (Project.FirstOrderSemantics.reduct M).mem p unit)
    (hCB : ConstructionProbeGateCap.Bounds unit C)
    (hVP : ∀ s d, PureKuratowski.PairMember M s d V → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p d) :
    ∃ Cap LC, MapsTo W R Cap ∧ ConstructionProbeGateCap.Graph D W mul G O C unit Cap ∧
      ConstructionProbeGateCap.Bounds unit Cap ∧ MapsTo W R LC ∧ Laws hM w D S zero W Q C V Cap LC ∧
      ConstructionProbeGateCap.Bounds unit LC ∧
      ∀ K, MapsTo W R K → Laws hM w D S zero W Q C V Cap K → K = LC := by
  obtain ⟨Cap,hCap,hcg,hCapB,_,_,_⟩ := ConstructionProbeGateCap.exists_cap hM hm hCon hO hC hu hun hCB
  obtain ⟨LC,hLC,hl⟩ := exists_cost hM hw hz hzw hQ hR hO hOld hC hV hCap hW hm.1.1
  exact ⟨Cap,LC,hCap,hcg,hCapB,hLC,hl,cost_bounds hM hw hz hzw hQ hR hW hLC hV hCap hCB hCapB hVP hl,
    fun K hK hk => cost_unique hM hw hz hzw hW hC hV hCap hK hLC hk hl⟩

end PPAC.Migration.ConstructionProbeCostFold

