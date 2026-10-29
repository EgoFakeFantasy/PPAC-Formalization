/- Pinned LocalRecords.relationClass_move:312-317 and labelClass_move:407-413.
Exact name action, not merely a forced equality. Consumer: the concrete
covariant family in LocalWitness.equal_of_record_eq and CodeCardinals.single. -/
import PPAC.Migration.ForcingRelationClass
import PPAC.Migration.ForcingLocalRecordEquality

namespace PPAC.Migration.ForcingRelationClassMove
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain)
open ForcingStabilizer (Action)
open ForcingSeparation (Separated)
open ForcingRelationClass (Class relationClass)
open ForcingHS (HS)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source separate_move, using the existing name-edge equation and full
forcing symmetry. No new collected-name or recursion implementation. -/
theorem separated_move (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi a sigma sigma' name name' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi a)
    (hs : ForcingNames.IsName (env (rho 6)) sigma)
    (hn' : ForcingNames.IsName (env (rho 6)) name')
    (hSigma : Action (env (rho 6)) a sigma sigma')
    (v v' : Fin n → M.Carrier .set) (hv : ∀ j, Action (env (rho 6)) a (v j) (v' j))
    (phi : Formula (n+1))
    (hc : Separated (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) sigma name phi)
    (hc' : Separated (orderFormula (rho 0) mul) (domain rho G F) env v' (env (rho 6)) sigma' name' phi) :
    Action (env (rho 6)) a name name' := by
  let W := env (rho 6)
  have har := ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp ha)
  have hfn := ForcingConditionAction.act_function (args2 W a) (0 : Fin 2) 1 har.1
  have htest (child image p q : M.Carrier .set) (him : Action W a child image)
      (hpW : (Project.FirstOrderSemantics.reduct M).mem p W) (hpq : PureKuratowski.PairMember M p q a) :
      (Forces false (orderFormula (rho 0) mul) env W child sigma p ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (Fin.lastCases child v) W p phi) ↔
      (Forces false (orderFormula (rho 0) mul) env W image sigma' q ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (Fin.lastCases image v') W q phi) := by
    refine and_congr ?_ ?_
    · exact ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha (.mem (0 : Fin 2) 1)
        (args2 child sigma) (args2 image sigma')
        (fun i => Fin.cases him (fun i => Fin.cases hSigma (fun j => Fin.elim0 j) i) i) hpW hpq
    · apply ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha phi _ _ _ hpW hpq
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.lastCases_last] using him
      · simpa only [Fin.lastCases_castSucc] using hv i
  obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM har.1 name
  have heq : out = name' := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    constructor
    · intro hz
      obtain ⟨child,p,image,q,he,him,hpq,hcode⟩ := (ForcingMapConditions.mem_mapping hM hfn hout z).mp hz
      obtain ⟨⟨c,hec⟩,hpW,hm,hf⟩ := (hc child p).mp he
      have hpq' := (ForcingConditionAction.act_inside hpW).mp
        ((ForcingConditionAction.relation_semantics (args2 W a) (0 : Fin 2) 1 p q).mp hpq)
      obtain ⟨image',c',hec',him',_⟩ := ForcingSeparation.entry_permute hM har.1 hs hSigma hec
      have hi := ForcingNameConjugacy.unique hM har.1 him' him
      subst image'
      have ht := (htest child image p q him hpW hpq').mp ⟨hm,hf⟩
      obtain ⟨z',hz',hz'm⟩ := (hc' image q).mpr ⟨⟨c',hec'⟩,har.1.2 p q hpq',ht.1,ht.2⟩
      exact (KuratowskiZF.code_unique hM hcode hz').symm ▸ hz'm
    · intro hz
      obtain ⟨image,q,hcode,hqW,_⟩ := ForcingNames.edges hn' z hz
      obtain ⟨⟨c',hec'⟩,_,hm,hf⟩ := (hc' image q).mp ⟨z,hcode,hz⟩
      obtain ⟨child,c,hec,him,_⟩ := (ForcingMapConditions.edge_mapping hM hfn hSigma image c').mp hec'
      obtain ⟨p,hpW,hpq⟩ := har.2.2 q hqW
      have ht := (htest child image p q him hpW hpq).mpr ⟨hm,hf⟩
      exact (ForcingMapConditions.mem_mapping hM hfn hout z).mpr
        ⟨child,p,image,q,(hc child p).mpr ⟨⟨c,hec⟩,hpW,ht.1,ht.2⟩,him,
          (ForcingConditionAction.relation_semantics (args2 W a) (0 : Fin 2) 1 p q).mpr (Or.inl ⟨hpW,hpq⟩),hcode⟩
  exact heq ▸ hout

theorem relationClass_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi a A A' E E' x x' name name' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi a)
    (hA : ForcingNames.IsName (env (rho 6)) A) (hn' : ForcingNames.IsName (env (rho 6)) name')
    (hAA : Action (env (rho 6)) a A A') (hEE : Action (env (rho 6)) a E E')
    (hxx : Action (env (rho 6)) a x x')
    (hc : Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) A E x name)
    (hc' : Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) A' E' x' name') :
    Action (env (rho 6)) a name name' :=
  separated_move hM env rho G F mul hp hG hF hpi ha hA hn' hAA (args2 E x) (args2 E' x')
    (fun i => Fin.cases hEE (fun i => Fin.cases hxx (fun j => Fin.elim0 j) i) i) _ hc hc'

/-- Exact class names are unique among genuine names, by their edge equation. -/
theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A E x name name' : M.Carrier .set}
    (hn : ForcingNames.IsName P name) (hn' : ForcingNames.IsName P name')
    (hc : Class R H env P A E x name) (hc' : Class R H env P A E x name') : name = name' := by
  have hsub {a b : M.Carrier .set} (ha : ForcingNames.IsName P a)
      (he : ∀ child p, PureKuratowski.PairMember M child p a → PureKuratowski.PairMember M child p b) :
      ForcingPowerName.Subset a b := by
    intro z hz
    obtain ⟨child,p,hcode,_,_⟩ := ForcingNames.edges ha z hz
    obtain ⟨z',hcode',hz'⟩ := he child p ⟨z,hcode,hz⟩
    exact (KuratowskiZF.code_unique hM hcode hcode').symm ▸ hz'
  exact (ModelTransfer.extensionality hM).eq_of_same_members name name' (fun z =>
    ⟨hsub hn (fun child p he => (hc' child p).mpr ((hc child p).mp he)) z,
      hsub hn' (fun child p he => (hc child p).mpr ((hc' child p).mp he)) z⟩)

/-- The concrete family j ↦ relationClass(labelSet,E,label j), with exact
name constructors. Membership in I retains the source index type. -/
def Value {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G F I K c t b labels E i name : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i I ∧ HS actionFormula v G (v 6) F name ∧
    ∃ x, ForcingLabelNames.Label (v 6) K c t i b x ∧ Class R H env (v 6) labels E x name

def value {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (rr : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F I K c t b labels E i name : Fin m) : Formula m :=
  (Formula.mem i I).conj ((ForcingHS.hs actionFormula rho G (rho 6) F name).conj
    (.ex ((ForcingLabelNames.label (rho 6).castSucc K.castSucc c.castSucc t.castSucc i.castSucc b.castSucc (Fin.last m)).conj
      (relationClass R H (paramsUp rr) (rho 6).castSucc labels.castSucc E.castSucc (Fin.last m) name.castSucc))))

theorem value_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (rr : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (G F I K c t b labels E i name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (value R H rr rho G F I K c t b labels E i name) ↔
      Value R H (fun j => env (rr j)) (fun j => env (rho j)) (env G) (env F) (env I) (env K)
        (env c) (env t) (env b) (env labels) (env E) (env i) (env name) := by
  simp only [value,Value,Formula.Realize,ForcingHS.hs_semantics (M := M),ForcingLabelNames.label_semantics (M := M),
    ForcingRelationClass.relationClass_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def family {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k) : Formula (k+2) :=
  let up := fun j : Fin k => j.castSucc.castSucc
  value (orderFormula (rho 0) mul) (domain rho G F) up (fun j => up (rho j))
    (up G) (up F) (up I) (up K) (up c) (up t) (up b) (up labels) (up E) (Fin.last k).castSucc (Fin.last (k+1))

theorem family_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul I K c t b labels E : Fin k) (i name : M.Carrier .set) :
    MapRel (family rho G F mul I K c t b labels E) env i name ↔
      Value (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env I) (env K) (env c) (env t) (env b) (env labels) (env E) i name := by
  unfold MapRel family
  rw [value_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {G F I K c t b labels E i name name' : M.Carrier .set}
    (hn : Value R H env v G F I K c t b labels E i name)
    (hn' : Value R H env v G F I K c t b labels E i name') : name = name' := by
  obtain ⟨_,hHS,x,hx,hclass⟩ := hn
  obtain ⟨_,hHS',x',hx',hclass'⟩ := hn'
  have he := ForcingLabelNames.unique hM hx hx'
  subst x'
  exact class_unique hM (ForcingHS.isName hHS) (ForcingHS.isName hHS') hclass hclass'

theorem value_exists (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu c t b labels E i : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hE : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) E)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i I) :
    ∃ name, Value (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
      (env G) (env F) I K c t b labels E i name := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM w mu).mpr hMu.2
  obtain ⟨hA,_⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hLabels
  obtain ⟨x,hx⟩ := ForcingLabelNames.exists_label hM hc (env (rho 6)) t i b
  have hX := ForcingLabelNames.label_HS hM (fun j => env (rho j)) hp hG hNormal hF hw hSmall hc ht hi hx
  obtain ⟨name,hn,hclass⟩ := ForcingRelationClass.exists_class hM env rho G F mul hp hG hNormal hA hE hX
  exact ⟨name,hi,hn,x,hx,hclass⟩

/-- Source labelClass_move, for the exact concrete family and moved E. -/
theorem labelClass_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu c t b labels E E' pi a i j name name' : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hpi : ForcingConditionGraphs.Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi a)
    (hEE : Action (env (rho 6)) a E E') (hij : PureKuratowski.PairMember M i j pi)
    (hn : Value (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
      (env G) (env F) I K c t b labels E i name)
    (hn' : Value (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
      (env G) (env F) I K c t b labels E' j name') : Action (env (rho 6)) a name name' := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  obtain ⟨hA,hAf⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hp hG hNormal hF hw
    ((ForcingSupportSize.native_small hM w mu).mpr hMu.2) hc ht hLabels
  obtain ⟨_,_,x,hx,hclass⟩ := hn
  obtain ⟨_,hHS',x',hx',hclass'⟩ := hn'
  have hxx := ForcingLabelNames.label_move hM (fun j => env (rho j)) hp ht hpi
    ((mapRel_action _ _ _).mp ha) hij hx hx'
  exact relationClass_move hM env rho G F mul hp hG hNormal hpi ha (ForcingHS.isName hA)
    (ForcingHS.isName hHS') (hAf pi ((hG pi).mpr hpi) a ha) hEE hxx hclass hclass'

theorem covariance (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul I K c t b labels E : Fin k)
    {B w mu J fixing : M.Carrier .set}
    (hp : Presentation (env (rho 0)) (env I) (env K) B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingSupportFilter.Filter (env I) (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (ht : ForcingWithTopCarrier.Empty (env t))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env t) (env b) (env labels))
    (hFix : ForcingLabelPermutations.Fixing (env G) J fixing)
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) fixing (env E)) :
    ForcingLocalRecordEquality.Covariant (family rho G F mul I K c t b labels E) env (fun j => env (rho j)) fixing := by
  intro pi a i j ni nj hpi ha hi hj hij
  have hAction := (mapRel_action (fun j => env (rho j)) pi a).mpr ha
  exact labelClass_move hM env rho G F mul hp hG hF hw hMu hc ht hLabels
    ((hG pi).mp ((hFix pi).mp hpi).1) hAction (hE pi hpi a hAction) hij
    ((family_semantics env rho G F mul I K c t b labels E i ni).mp hi)
    ((family_semantics env rho G F mul I K c t b labels E j nj).mp hj)

/-- Total, single-valued and covariant on the actual internal index set. -/
def systemResult {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K c t b labels E fixing : Fin k) : Project.Formula 1 k :=
  let f := family rho G F mul I K c t b labels E
  .conj (.forallE (.imp (.mem (.bound 0) (.bound I.succ))
    (.existsE (ProjectSyntax.encode id (ReplacementPredicates.rel f (fun j => j.succ.succ) 1 0)))))
    (.conj (.forallE (.forallE (.forallE
      (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel f (fun j => j.succ.succ.succ) 2 1))
        (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel f (fun j => j.succ.succ.succ) 2 0))
          (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))
      (ForcingLocalRecordEquality.covariant f id rho fixing))

theorem systemResult_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (G F mul I K c t b labels E fixing : Fin k) :
    (systemResult rho G F mul I K c t b labels E fixing).FreeClosed := by
  simp -implicitDefEqProofs [systemResult,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingLocalRecordEquality.covariant_freeClosed]

theorem systemResult_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (rho : Fin 7 → Fin k) (G F mul I K c t b labels E fixing : Fin k)
    (env : Env (Project.FirstOrderSemantics.reduct M) k) :
    Project.Formula.satisfies env (systemResult rho G F mul I K c t b labels E fixing) ↔
      (∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env.bound I) →
        ∃ name, MapRel (family rho G F mul I K c t b labels E) env.bound i name) ∧
      (∀ i name name', MapRel (family rho G F mul I K c t b labels E) env.bound i name →
        MapRel (family rho G F mul I K c t b labels E) env.bound i name' → name = name') ∧
      ForcingLocalRecordEquality.Covariant (family rho G F mul I K c t b labels E) env.bound
        (fun j => env.bound (rho j)) (env.bound fixing) := by
  simp only [systemResult,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingMapConditions.rel_semantics (M := M),
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ForcingLocalRecordEquality.covariant_semantics hM]
  rfl

def systemSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu c t b labels E J fixing G F mul : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
      (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
      (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
      (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels))
      (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G J fixing))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing E))
      (systemResult rho G F mul I K c t b labels E fixing))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed,systemResult_freeClosed]

theorem system_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu c t b labels E J fixing G F mul : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (systemSentence rho I K B w mu c t b labels E J fixing G F mul)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (systemSentence rho I K B w mu c t b labels E J fixing G F mul)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),systemResult_semantics hM]
  intro hw hMu hp hG hF hc ht hLabels hE hFix hEf
  refine ⟨?_,?_,covariance hM env rho G F mul I K c t b labels E hp hG hF hw hMu hc ht hLabels hFix hEf⟩
  · intro i hi
    obtain ⟨name,hn⟩ := value_exists hM env rho G F mul hp hG hF hw hMu hc ht hLabels hE hi
    exact ⟨name,(family_semantics env rho G F mul I K c t b labels E i name).mpr hn⟩
  · intro i name name' hn hn'
    exact value_unique hM ((family_semantics env rho G F mul I K c t b labels E i name).mp hn)
      ((family_semantics env rho G F mul I K c t b labels E i name').mp hn')

theorem system_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w mu c t b labels E J fixing G F mul : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (systemSentence rho I K B w mu c t b labels E J fixing G F mul)) :=
  ModelTransfer.derives (fun _ hM => system_models rho I K B w mu c t b labels E J fixing G F mul hM)

/- Instantiate the already proved same-record quotient endpoint with this exact
family; covariance is now derived from concrete label data and E support. -/
def recordSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta c top bit labels E : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection root (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection t (rho 0) I))
    (.imp (.mem (.bound b) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s b root))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul t b root))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge s x i))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge t x j))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) root A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A fixing))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing sigma))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing tau))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixing E))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (family rho G F mul I K c top bit labels E) id i ni))
    (.imp (ProjectSyntax.encode id (ReplacementPredicates.rel (family rho G F mul I K c top bit labels E) id j nj))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d1))
    (.imp (ForcingLocalRecordPullback.supported (rho 0) s d0)
    (.imp (ForcingLocalRecordPullback.supported (rho 0) t d1)
    (.imp (ForcingLocalRecordPullback.pullback (rho 0) s d0 pb)
    (.imp (ForcingLocalRecordPullback.pullback (rho 0) t d1 pb)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 s))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z1 d1 t))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) sigma ni z0))
    (.imp (ProjectSyntax.encode id (ForcingAtomicRelations.forces true (orderFormula (rho 0) mul) id (rho 6) tau nj z1))
    (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g))
    (.imp (.mem (.bound d1) (.bound g))
    (.imp (ProjectSyntax.encode id (ForcingLocalQuotient.projection (orderFormula (rho 0) mul) id (rho 6) g root X pr))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr sigma alpha))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr tau beta))
    (Project.Formula.extensionalEq (.bound alpha) (.bound beta)))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
    Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
    ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
    ForcingLocalRecordPullback.supported_freeClosed,ForcingLocalRecordPullback.pullback_freeClosed]

theorem record_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta c top bit labels E : Fin k) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence (recordSentence rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta c top bit labels E) := by
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.sub_semantics (M := M),KuratowskiZF.source_edge,ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingMapConditions.rel_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ForcingLocalRecordPullback.pullback_semantics hM,
    ForcingSupportingRoot.code_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),ForcingLocalAtomic.cohenFilter_semantics (M := M),ForcingLocalQuotient.projection_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  intro hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot hs ht hb hsroot htroot hxi hxj hRange hFix hSigma hTau hc htop hLabels hEf hni hnj hd0 hd1 hds hdt hpb0 hpb1 hz0 hz1 he0 he1 hg hd1g hPr hAlpha hBeta
  have hCov := covariance hM bound rho G F mul I K c top bit labels E hpres hG hFilter hw hMu hc htop hLabels hFix hEf
  exact ForcingLocalRecordEquality.quotient_equal hM hChoice (family rho G F mul I K c top bit labels E) bound rho G F mul hw hMu hI hD hMergers hRow hm hpres hG hFilter hroot hs ht hb hsroot htroot hxi hxj hRange hFix hSigma hTau hCov hni hnj hd0 hd1 hds hdt hpb0 hpb1 hz0 hz1 he0 he1 hg hd1g hPr hAlpha hBeta

theorem record_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta c top bit labels E : Fin k) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (recordSentence rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta c top bit labels E))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let zero := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => zero⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact record_models rho w mu history kappa e mark H C incoming base I K B G F mul root s t b x i j A fixing d0 d1 pb z0 z1 sigma tau ni nj g X pr alpha beta c top bit labels E hL hChoice


end PPAC.Migration.ForcingRelationClassMove
