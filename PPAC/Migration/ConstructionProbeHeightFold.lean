/- Pinned ProbeMargins.rawHeight and Word.height: reuse the accepted actual
Raw evalHom and Word lift, with affine height as its binary algebra. No
new history, finite-recursion backend or external-length induction. -/
import PPAC.Migration.ConstructionProbeHeightOperation
import PPAC.Migration.ConstructionProbeHomExt

namespace PPAC.Migration.ConstructionProbeHeightFold
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionProbeRaw
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeHeightOperation (Affine)
open ConstructionProbeHomEvaluation (Eval Prepend)
open ConstructionProbeHomEvaluationSyntax (LiftGraph)
open ConstructionProbeLetters (Representatives)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Refine the existing evalHom's range using the actual old and operation
ranges. This needs only its already constructed root step, not new induction. -/
theorem eval_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S R N J G H Id q y : M.Carrier .set}
    (hH : MapsTo D R H) (hG : MapsTo J R G) (hy : Eval hM w D S N G H Id q y) :
    (Project.FirstOrderSemantics.reduct M).mem y R := by
  obtain ⟨n,m,f,x,history,_,_,hmn,_,_,_,hh,hy⟩ := hy
  obtain ⟨historyPrefix,_,hStep⟩ := hh.2 n hmn.predecessor_mem y hy
  obtain ⟨k,_,_,hStep⟩ := hStep
  rcases hStep with ⟨_,hy⟩ | ⟨j,s,v,_,_,_,hy⟩
  · exact hH.2 x y hy
  · exact ConstructionProbeHomEvaluation.prepend_range hG hy

theorem prepend_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R S zero O V N G Id s v y : M.Carrier .set}
    (hSN : Subset S N) (hRN : Subset R N)
    (hi : ForcingConditionGraphs.IdentityGraph S Id)
    (hg : ConstructionProbeHeightOperation.Graph hM w Q R S zero O V N G)
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) (hv : (Project.FirstOrderSemantics.reduct M).mem v R) :
    Prepend Id G s v y ↔ Affine hM w Q O V s v y := by
  constructor
  · rintro ⟨a,ha,hprod⟩
    have he := ((hi s a).mp ha).2
    subst a
    rcases ((hg s v y).mp hprod).2.2 with ⟨_,h⟩ | ⟨hn,_⟩
    · exact h
    · exact (hn ⟨hs,hv⟩).elim
  · intro ha
    exact ⟨s,(hi s s).mpr ⟨hs,rfl⟩,(hg s v y).mpr ⟨hSN s hs,hRN v hv,Or.inl ⟨⟨hs,hv⟩,ha⟩⟩⟩

def Laws (hM : FirstOrder.Theory.Models M nativeZF) (w D S zero W Q H O V L : M.Carrier .set) : Prop :=
  (∀ x q y, Old zero D x q →
    (PureKuratowski.PairMember M q y L ↔ PureKuratowski.PairMember M x y H)) ∧
  (∀ s t q y, Cons w D S s t q → (Project.FirstOrderSemantics.reduct M).mem q W →
    (PureKuratowski.PairMember M q y L ↔ ∃ v, PureKuratowski.PairMember M t v L ∧ Affine hM w Q O V s v y))

theorem height_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R H O V N J G Id L : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hSN : Subset S N) (hRN : Subset R N)
    (hJ : Representatives N N J) (hG : MapsTo J R G)
    (hGN : MapsTo J N G) (hH : MapsTo D R H) (hHN : MapsTo D N H) (hId : MapsTo S N Id)
    (hi : ForcingConditionGraphs.IdentityGraph S Id)
    (hg : ConstructionProbeHeightOperation.Graph hM w Q R S zero O V N G)
    (hl : LiftGraph hM w D S N G H Id W L) : Laws hM w D S zero W Q H O V L := by
  have hWords := ConstructionProbeWord.word_laws hM hw hz hzw hW
  constructor
  · intro x q y hOld
    constructor
    · intro hy
      exact ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOld ((hl q y).mp hy).2
    · intro hy
      exact (hl q y).mpr ⟨hWords.1 x q hOld,
        (ConstructionProbeHomEvaluation.eval_old_iff hM hw hz hzw hJ hGN hHN hId hOld).mpr hy⟩
  · intro s t q y hCons hqW
    have htW := ((hWords.2.1 s t q hCons).mp hqW).1
    have hs : (Project.FirstOrderSemantics.reduct M).mem s S := by
      obtain ⟨n,m,f,g,x,hn,hm,hmn,hf,hg,hx,hs,ht,hq,happ⟩ := hCons
      exact hs
    constructor
    · intro hy
      obtain ⟨v,hv,hprep⟩ := ConstructionProbeHomEvaluation.eval_cons_forward hM hw hCons ((hl q y).mp hy).2
      exact ⟨v,(hl t v).mpr ⟨htW,hv⟩,
        (prepend_iff hM hSN hRN hi hg hs (eval_range hM hH hG hv)).mp hprep⟩
    · rintro ⟨v,hv,ha⟩
      have hvEval := ((hl t v).mp hv).2
      exact (hl q y).mpr ⟨hqW,
        (ConstructionProbeHomEvaluation.eval_cons_iff hM hw hJ hGN hHN hId hCons).mpr
          ⟨v,hvEval,(prepend_iff hM hSN hRN hi hg hs (eval_range hM hH hG hvEval)).mpr ha⟩⟩

/-- The source actual Word height map, on the same Word carrier and with
literal old/cons equations. Neither a height graph nor a fold is assumed. -/
theorem exists_height (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R H O V : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hH : MapsTo D R H) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hW : WordCarrier w D S mul A b W) :
    ∃ L, MapsTo W R L ∧ Laws hM w D S zero W Q H O V L := by
  have hZeroR : (Project.FirstOrderSemantics.reduct M).mem zero R := by
    obtain ⟨z,hz',⟨q,hq,hp⟩,_⟩ := ConstructionFractionDifference.principal_zero_exists hM hw hQ
    have he : zero = z := (ModelTransfer.extensionality hM).eq_of_same_members zero z
      (fun p => ⟨fun h => (hz p h).elim,fun h => (hz' p h).elim⟩)
    rw [he]
    exact (hR z).mpr (principal_cut hM hw hQ hq hp)
  obtain ⟨N,hN⟩ := KP.exists_unionOfTwo (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) S R
  have hSN : Subset S N := fun s hs => (hN s).mpr (Or.inl hs)
  have hRN : Subset R N := fun r hr => (hN r).mpr (Or.inr hr)
  obtain ⟨J,G,hJ,hG,hg⟩ := ConstructionProbeHeightOperation.exists_operation hM hw hQ hR hO hV hZeroR N
  have hGN : MapsTo J N G := ⟨hG.1,fun p y hy => hRN y (hG.2 p y hy)⟩
  have hHN : MapsTo D N H := ⟨hH.1,fun x y hy => hRN y (hH.2 x y hy)⟩
  obtain ⟨Id,hIdPerm,hi⟩ := ForcingConditionGraphs.exists_identity hM S
  have hId : MapsTo S N Id := ⟨hIdPerm.1.1,fun x y hy => hSN y (hIdPerm.1.2 x y hy)⟩
  obtain ⟨L,hL,hl⟩ := ConstructionProbeHomEvaluationSyntax.exists_lift_graph hM hw hJ hGN hHN hId hW
  have hLR : MapsTo W R L := ⟨hL.1,fun q y hy => eval_range hM hH hG ((hl q y).mp hy).2⟩
  exact ⟨L,hLR,height_laws hM hw hz hzw hW hSN hRN hJ hG hGN hH hHN hId hi hg hl⟩

/-- Source recurrence uniquely determines the actual height graph. Reuse
existing formula-indexed Raw induction and its agreement formula. -/
theorem height_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R H O V L K : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W) (hH : MapsTo D R H) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hL : MapsTo W R L) (hK : MapsTo W R K)
    (hl : Laws hM w D S zero W Q H O V L) (hk : Laws hM w D S zero W Q H O V K) : L = K := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases W (Fin.cases L (fun _ => K))
    free := fun _ => w }
  let p : Project.UnarySchema 3 := {
    body := ConstructionProbeHomExt.agreement 1 2 3 0
    freeClosed := ConstructionProbeHomExt.agreement_freeClosed _ _ _ _ }
  have he (q : M.Carrier .set) : p.denote env q ↔
      ((Project.FirstOrderSemantics.reduct M).mem q W → ConstructionProbeHomExt.AgreeAt q L K) :=
    ConstructionProbeHomExt.agreement_semantics hM (env.push q) 1 2 3 0
  have hWords := ConstructionProbeWord.word_laws hM hw hz hzw hW
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro x q hOld
    apply (he q).mpr
    intro _ y z hy hzv
    exact ForcingConditionGraphs.function_unique hH.1 ((hl.1 x q y hOld).mp hy) ((hk.1 x q z hOld).mp hzv)) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro hq y z hy hzv
    have ht := ((hWords.2.1 s t q hCons).mp hq).1
    obtain ⟨v,hv,ha⟩ := (hl.2 s t q y hCons hq).mp hy
    obtain ⟨v',hv',ha'⟩ := (hk.2 s t q z hCons hq).mp hzv
    have hvv := (he t).mp ih ht v v' hv hv'
    subst v'
    exact ConstructionProbeHeightOperation.affine_unique hM hO hV ha ha')
  have hAgree := fun q hq => (he q).mp (hAll q (ConstructionProbeWord.word_raw hW hq)) hq
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM W R L).mp hL).1.1
    ((ForcingSupportSize.native_mapsTo hM W R K).mp hK).1.1
  intro q y
  constructor
  · intro hy
    have hq := ForcingConditionGraphs.function_input hL.1 hy
    obtain ⟨z,hzv,_⟩ := hK.1.2 q hq
    exact (hAgree q hq y z hy hzv).symm ▸ hzv
  · intro hy
    have hq := ForcingConditionGraphs.function_input hK.1 hy
    obtain ⟨z,hzv,_⟩ := hL.1.2 q hq
    exact (hAgree q hq z y hzv hy) ▸ hzv

theorem existsUnique_height (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W Q R H O V : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hH : MapsTo D R H) (hO : MapsTo S R O) (hV : MapsTo S R V)
    (hW : WordCarrier w D S mul A b W) :
    ∃ L, MapsTo W R L ∧ Laws hM w D S zero W Q H O V L ∧
      ∀ K, MapsTo W R K → Laws hM w D S zero W Q H O V K → K = L := by
  obtain ⟨L,hL,hl⟩ := exists_height hM hw hz hzw hQ hR hH hO hV hW
  exact ⟨L,hL,hl,fun K hK hk => height_unique hM hw hz hzw hW hH hO hV hK hL hk hl⟩

end PPAC.Migration.ConstructionProbeHeightFold
