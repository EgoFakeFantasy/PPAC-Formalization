/- Pinned ProductNames.label/label_raw/smul_label (241-260).
Consumers: labelSet and LocalQuotients.labelSet_subsetBound/localName_descent.
Use the existing check recursion, native functional image/function graph,
collected-name constructor, concrete Bit and actual condition action. -/
import PPAC.Migration.ForcingProductBits
import PPAC.Migration.ForcingHSCheck

namespace PPAC.Migration.ForcingLabelNames
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingConditionGraphs (FunctionOn Permutation)
open ForcingCheckName (Checked)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingMapConditions (MapRel)
open ForcingProductBits (Bit)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (c t i name : M.Carrier .set) : Prop :=
  ∃ x, PureKuratowski.PairMember M i x c ∧ Checked t x name

def value {k : Nat} (c t i name : Fin k) : Formula k :=
  .ex ((Source.SetLanguage.edge c.castSucc i.castSucc (Fin.last k)).conj
    (ForcingCheckName.checkName t.castSucc (Fin.last k) name.castSucc))

theorem value_semantics {k : Nat} (env : Fin k → M.Carrier .set) (c t i name : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (value c t i name) ↔
      Value (env c) (env t) (env i) (env name) := by
  simp only [value,Value,Formula.Realize,KuratowskiZF.source_edge,
    ForcingCheckName.checkName_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def CheckFamily (K c t f : M.Carrier .set) : Prop :=
  FunctionOn K f ∧ ∀ i name, PureKuratowski.PairMember M i name f ↔
    (Project.FirstOrderSemantics.reduct M).mem i K ∧ Value c t i name

theorem exists_checkFamily (hM : FirstOrder.Theory.Models M nativeZF)
    {K c : M.Carrier .set} (hc : FunctionOn K c) (t : M.Carrier .set) :
    ∃ f, CheckFamily (M := M) K c t f := by
  let params := args2 c t
  let query := value (0 : Fin 4) 1 2 3
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    { bound := fun i => params i.rev, free := fun _ => K }
  have hRel : ∀ i name, (ProjectSyntax.binary query).denote env i name ↔ Value c t i name := by
    intro i name
    rw [ForcingMapConditions.binary_semantics hM query params K i name]
    simp only [MapRel,query,value_semantics (M := M),params]
    rfl
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i K →
      ∃ name, (ProjectSyntax.binary query).denote env i name := by
    intro i hi
    obtain ⟨x,hix,_⟩ := hc.2 i hi
    obtain ⟨name,hn⟩ := ForcingCheckName.exists_checked hM t x
    exact ⟨name,(hRel i name).mpr ⟨x,hix,hn⟩⟩
  have hu : ∀ i a b, (ProjectSyntax.binary query).denote env i a →
      (ProjectSyntax.binary query).denote env i b → a = b := by
    intro i a b ha hb
    obtain ⟨x,hix,ha⟩ := (hRel i a).mp ha
    obtain ⟨y,hiy,hb⟩ := (hRel i b).mp hb
    have e := ForcingConditionGraphs.function_unique hc hix hiy
    exact ForcingCheckName.unique hM ha (e.symm ▸ hb)
  obtain ⟨bound,hbound⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM)
    (ProjectSyntax.binary query) env K ht hu
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    (ProjectSyntax.binary query) env (source := K) (target := bound) ht
    (fun i _ a b ha hb => hu i a b ha hb)
    (fun i name hi hn => (hbound name).mpr ⟨i,hi,hn⟩)
  exact ⟨f,((ForcingSupportSize.native_mapsTo hM K bound f).mpr hf).1,
    fun i name => (he i name).trans (and_congr Iff.rfl (hRel i name))⟩

def bitPredicate : Formula 5 := ForcingProductBits.bit 0 4 1 3 2

theorem bitPredicate_semantics (W j b i p : M.Carrier .set) :
    MapRel bitPredicate (args3 W j b) i p ↔ Bit W p j i b := by
  simp only [MapRel,bitPredicate,ForcingProductBits.bit_semantics (M := M)]
  rfl

def Admissible (W K c t j b child p : M.Carrier .set) : Prop :=
  ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K ∧ Value c t i child ∧ Bit W p j i b

def admissible {k : Nat} (W K c t j b child p : Fin k) : Formula k :=
  .ex ((Formula.mem (Fin.last k) K.castSucc).conj
    ((value c.castSucc t.castSucc (Fin.last k) child.castSucc).conj
      (ForcingProductBits.bit W.castSucc p.castSucc j.castSucc (Fin.last k) b.castSucc)))

theorem admissible_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (W K c t j b child p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (admissible W K c t j b child p) ↔
      Admissible (env W) (env K) (env c) (env t) (env j) (env b) (env child) (env p) := by
  simp only [admissible,Admissible,Formula.Realize,value_semantics (M := M),
    ForcingProductBits.bit_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]

def Entry (W K c t j b z : M.Carrier .set) : Prop :=
  ∃ child p, Admissible W K c t j b child p ∧ PureKuratowski.Code M z child p

def entry {k : Nat} (W K c t j b z : Fin k) : Formula k :=
  .ex (.ex ((admissible W.castSucc.castSucc K.castSucc.castSucc c.castSucc.castSucc
    t.castSucc.castSucc j.castSucc.castSucc b.castSucc.castSucc
    (Fin.last k).castSucc (Fin.last (k+1))).conj
      (PairSyntax.ordered z.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1)))))

theorem entry_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W K c t j b z : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (entry W K c t j b z) ↔
      Entry (env W) (env K) (env c) (env t) (env j) (env b) (env z) := by
  simp only [entry,Entry,Formula.Realize,admissible_semantics (M := M),KuratowskiZF.source_code,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Literal source label_raw: exactly the checked indices with the given bit.
There is no rank cutoff, chosen external family or assumed collection name. -/
def Label (W K c t j b name : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z name ↔ Entry W K c t j b z

def label {k : Nat} (W K c t j b name : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) name.castSucc).iff
    (entry W.castSucc K.castSucc c.castSucc t.castSucc j.castSucc b.castSucc (Fin.last k)))

theorem label_semantics {k : Nat} (env : Fin k → M.Carrier .set) (W K c t j b name : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (label W K c t j b name) ↔
      Label (env W) (env K) (env c) (env t) (env j) (env b) (env name) := by
  simp only [label,Label,Source.Formula.iff,Formula.Realize,entry_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨(h z).1,(h z).2⟩,fun h z => ⟨(h z).mp,(h z).mpr⟩⟩

theorem admissible_collected_iff {W K c t j b f child p : M.Carrier .set}
    (hf : CheckFamily K c t f) :
    ForcingCollectedName.Admissible bitPredicate (args3 W j b) K f W child p ↔
      Admissible W K c t j b child p := by
  constructor
  · rintro ⟨_,i,hi,hic,hbit⟩
    exact ⟨i,hi,((hf.2 i child).mp hic).2,(bitPredicate_semantics W j b i p).mp hbit⟩
  · rintro ⟨i,hi,hic,hbit⟩
    exact ⟨hbit.1,i,hi,(hf.2 i child).mpr ⟨hi,hic⟩,(bitPredicate_semantics W j b i p).mpr hbit⟩

theorem collected_iff {W K c t j b f name : M.Carrier .set} (hf : CheckFamily K c t f) :
    ForcingCollectedName.Collected bitPredicate (args3 W j b) K f W name ↔ Label W K c t j b name := by
  simp only [ForcingCollectedName.Collected,ForcingCollectedName.Entry,Label,Entry,
    admissible_collected_iff hf]

theorem exists_label (hM : FirstOrder.Theory.Models M nativeZF)
    {K c : M.Carrier .set} (hc : FunctionOn K c) (W t j b : M.Carrier .set) :
    ∃ name, Label (M := M) W K c t j b name := by
  obtain ⟨f,hf⟩ := exists_checkFamily hM hc t
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM bitPredicate (args3 W j b) K f W
  exact ⟨name,(collected_iff hf).mp hn⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {W K c t j b a n : M.Carrier .set} (ha : Label W K c t j b a) (hn : Label W K c t j b n) : a = n :=
  (ModelTransfer.extensionality hM).eq_of_same_members a n (fun z => (ha z).trans (hn z).symm)

theorem edge_label (hM : FirstOrder.Theory.Models M nativeZF)
    {W K c t j b name : M.Carrier .set} (hn : Label W K c t j b name) (child p : M.Carrier .set) :
    PureKuratowski.PairMember M child p name ↔ Admissible W K c t j b child p := by
  constructor
  · rintro ⟨z,hc,hz⟩
    obtain ⟨x,q,ha,hc'⟩ := (hn z).mp hz
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hc'
    exact ha
  · intro ha
    obtain ⟨z,hc⟩ := KuratowskiZF.exists_code hM child p
    exact ⟨z,hc,(hn z).mpr ⟨child,p,ha,hc⟩⟩

theorem isName (hM : FirstOrder.Theory.Models M nativeZF)
    {W K c t j b name : M.Carrier .set}
    (ht : (Project.FirstOrderSemantics.reduct M).mem t W) (hn : Label W K c t j b name) :
    ForcingNames.IsName W name := by
  apply ForcingNames.intro_name hM W name
  intro z hz
  obtain ⟨child,p,⟨i,_,⟨x,_,hx⟩,hb⟩,hc⟩ := (hn z).mp hz
  exact ⟨child,p,hc,hb.1,ForcingCheckNameLaws.isName hM ht x child hx⟩

theorem checked_fixed (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w t pi A x name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (ht : ForcingWithTopCarrier.Empty t) (hA : ForcingProductFamily.Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi A)
    (hn : Checked t x name) : ForcingStabilizer.Action (v 6) A name name := by
  have ha := (ForcingProductFamily.action_permutation hA).1
  obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM ha name
  have hfix : ForcingConditionAction.Act (v 6) A t t :=
    Or.inl ⟨(hp.2.2.2.2.2 t).mpr (Or.inl ht),ForcingProductFamily.top_fixed hp ht hA⟩
  have e := ForcingCheckNameLaws.action_fixed hM (args2 (v 6) A) (0 : Fin 2) 1 ha hfix hn hout
  exact e ▸ hout

/-- Source smul_label, proved from actual map membership and Bit movement. -/
theorem label_move (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w c t j j' b pi A name name' : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (ht : ForcingWithTopCarrier.Empty t) (hpi : Permutation I pi)
    (hA : ForcingProductFamily.Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi A)
    (hjj : PureKuratowski.PairMember M j j' pi)
    (hn : Label (v 6) K c t j b name) (hn' : Label (v 6) K c t j' b name') :
    ForcingStabilizer.Action (v 6) A name name' := by
  have ha := ForcingProductFamily.action_permutation hA
  have hfn := ForcingConditionAction.act_function (args2 (v 6) A) (0 : Fin 2) 1 ha.1
  obtain ⟨out,hout⟩ := ForcingNameConjugacy.exists_action hM ha.1 name
  have hEq : out = name' := by
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    constructor
    · intro hz
      obtain ⟨child,p,image,q,he,hm,hq,hcode⟩ := (ForcingMapConditions.mem_mapping hM hfn hout z).mp hz
      obtain ⟨i,hi,hval,hbit⟩ := (edge_label hM hn child p).mp he
      obtain ⟨x,hix,hchecked⟩ := hval
      have e := ForcingNameConjugacy.unique hM ha.1 hm (checked_fixed hM v hp ht hA hchecked)
      subst image
      have hpq := (ForcingConditionAction.act_inside hbit.1).mp
        ((ForcingConditionAction.relation_semantics (args2 (v 6) A) (0 : Fin 2) 1 p q).mp hq)
      exact (hn' z).mpr ⟨child,q,⟨i,hi,⟨x,hix,hchecked⟩,(ForcingProductBits.bit_move hM hp hpi hA hpq hjj).mpr hbit⟩,hcode⟩
    · intro hz
      obtain ⟨child,q,⟨i,hi,hval,hbit⟩,hcode⟩ := (hn' z).mp hz
      obtain ⟨p,hpW,hpq⟩ := ha.2.2 q hbit.1
      obtain ⟨x,hix,hchecked⟩ := hval
      have hb := (ForcingProductBits.bit_move hM hp hpi hA hpq hjj).mp hbit
      exact (ForcingMapConditions.mem_mapping hM hfn hout z).mpr
        ⟨child,p,child,q,(edge_label hM hn child p).mpr ⟨i,hi,⟨x,hix,hchecked⟩,hb⟩,
          checked_fixed hM v hp ht hA hchecked,
          (ForcingConditionAction.relation_semantics (args2 (v 6) A) (0 : Fin 2) 1 p q).mpr
            (Or.inl ⟨hpW,hpq⟩),hcode⟩
  exact hEq ▸ hout

/-- The source singleton support is actually small, using the given omega bound
and the original constant-function constructor, with no new cardinal theorem. -/
theorem singleton_small (hM : FirstOrder.Theory.Models M nativeZF)
    {w mu j S : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hS : ForcingWithTopCarrier.Single S j) : ForcingSupportSize.Small S mu := by
  obtain ⟨z,_,hz⟩ := hw.1.1
  obtain ⟨q,hq⟩ := hSmall
  obtain ⟨v,hzv,_⟩ := hq.1.1.2 z hz
  have hv := hq.1.2 z v hzv
  obtain ⟨f,hf,_⟩ := ZF.exists_constantFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (source := S) hv
  exact ⟨f,((ForcingSupportSize.native_mapsTo hM S mu f).mpr hf),fun a b v ha hb =>
    ((hS a).mp (hf.input_mem_of_pairMember ha)).trans ((hS b).mp (hf.input_mem_of_pairMember hb)).symm⟩

theorem label_HS (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w mu G F c t j b name : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hNormal : ForcingNormalFilter.Normal I G F)
    (hFilter : ForcingSupportFilter.Filter I G mu F)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hSmall : ForcingSupportSize.Small w mu)
    (hc : FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j I) (hn : Label (v 6) K c t j b name) :
    ForcingHS.HS actionFormula v G (v 6) F name := by
  obtain ⟨S,hS⟩ := ForcingWithTopCarrier.exists_single hM j
  have hSI : (Project.FirstOrderSemantics.reduct M).MemberSubset S I :=
    fun x hx => ((hS x).mp hx).symm ▸ hj
  obtain ⟨H,hH⟩ := ForcingLabelPermutations.exists_fixing hM G S
  have hSub := ForcingConjugationGraph.fixing_subgroup hM hG hH hSI
  have hHF := (hFilter H).mpr ⟨hSub,S,H,hSI,singleton_small hM hw hSmall hS,hH,fun _ h => h⟩
  obtain ⟨f,hf⟩ := exists_checkFamily hM hc t
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  have hFamily : ForcingCollectedHS.FamilyHS v G (v 6) F K f := by
    intro i child _ hic
    obtain ⟨x,_,hx⟩ := ((hf.2 i child).mp hic).2
    exact ForcingHSCheck.check_hs hM actionFormula v G (v 6) F t hNormal.1 htW (by
      intro g hg
      obtain ⟨A,hA⟩ := ForcingProductFamily.exists_action hM hp ((hG g).mp hg)
      exact ⟨A,(mapRel_action v g A).mpr hA,(ForcingProductFamily.action_permutation hA).1,
        Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht hA⟩⟩) x child hx
  have hIndex : ForcingCollectedHS.IndexedPermutes bitPredicate (args3 (v 6) j b) v H K f (v 6) := by
    intro g hg A hga i child p hi hic hpW hbit
    have hAg := (mapRel_action v g A).mp hga
    have hperm := ForcingProductFamily.action_permutation hAg
    obtain ⟨q,hpq,_⟩ := hperm.1.1.2 p hpW
    obtain ⟨hgG,hgFix⟩ := (hH g).mp hg
    have hjj := hgFix j ((hS j).mpr rfl)
    obtain ⟨x,_,hx⟩ := ((hf.2 i child).mp hic).2
    exact ⟨i,child,q,hi,hic,(bitPredicate_semantics (v 6) j b i q).mpr
      ((ForcingProductBits.bit_move hM hp ((hG g).mp hgG) hAg hpq hjj).mpr
        ((bitPredicate_semantics (v 6) j b i p).mp hbit)),
      checked_fixed hM v hp ht hAg hx,hpq⟩
  exact ForcingCollectedHS.collect_HS hM bitPredicate (args3 (v 6) j b) v hp hG hNormal hSub hHF hFamily
    ((ForcingCollectedHS.indexed_permutes_iff hM bitPredicate (args3 (v 6) j b) v H K f).mp hIndex)
    ((collected_iff hf).mpr hn)

def existenceSentence : Source.Sentence :=
  ((Source.SetLanguage.functionOn (2 : Fin 6) 1).imp (.ex (label 0 1 2 3 4 5 6))).close

theorem existence_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence existenceSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hc
  obtain ⟨name,hn⟩ := exists_label hM ((ForcingConditionGraphs.functionOn_semantics (M := M) env 1 2).mp hc)
    (env 0) (env 3) (env 4) (env 5)
  refine ⟨name,?_⟩
  apply (label_semantics (M := M) (Fin.lastCases name env)
    (0 : Fin 6).castSucc (1 : Fin 6).castSucc (2 : Fin 6).castSucc
    (3 : Fin 6).castSucc (4 : Fin 6).castSucc (5 : Fin 6).castSucc (Fin.last 6)).mpr
  simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hn

theorem existence_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence existenceSentence) :=
  ModelTransfer.derives (fun _ hM => existence_models hM)

def uniquenessSentence : Source.Sentence :=
  ((label (0 : Fin 8) 1 2 3 4 5 6).imp ((label 0 1 2 3 4 5 7).imp (.equal 6 7))).close

theorem uniqueness_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence uniquenessSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env ha hb
  exact unique hM ((label_semantics (M := M) env 0 1 2 3 4 5 6).mp ha)
    ((label_semantics (M := M) env 0 1 2 3 4 5 7).mp hb)

theorem uniqueness_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence uniquenessSentence) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models hM)

def moveSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w c t j j' b pi A name name' : Fin k) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingWithTopCarrier.empty t).imp
      ((ForcingConditionGraphs.permutation I pi).imp
        ((ReplacementPredicates.rel actionFormula rho pi A).imp
          ((Source.SetLanguage.edge pi j j').imp
            ((label (rho 6) K c t j b name).imp
              ((label (rho 6) K c t j' b name').imp
                (ForcingStabilizer.action (rho 6) A name name')))))))).close

theorem move_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w c t j j' b pi A name name' : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (moveSentence rho I K B w c t j j' b pi A name name')).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp ht hpi hA hjj hn hn'
  apply (ForcingStabilizer.action_semantics (M := M) env (rho 6) A name name').mpr
  exact label_move hM (fun i => env (rho i))
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht)
    ((ForcingConditionGraphs.permutation_semantics (M := M) env I pi).mp hpi)
    ((mapRel_action _ _ _).mp ((ForcingMapConditions.rel_semantics (M := M) env actionFormula rho pi A).mp hA))
    ((KuratowskiZF.source_edge (M := M) env pi j j').mp hjj)
    ((label_semantics (M := M) env (rho 6) K c t j b name).mp hn)
    ((label_semantics (M := M) env (rho 6) K c t j' b name').mp hn')

theorem move_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w c t j j' b pi A name name' : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (moveSentence rho I K B w c t j j' b pi A name name')) :=
  ModelTransfer.derives (fun _ hM => move_models rho I K B w c t j j' b pi A name name' hM)

def result {k : Nat} (rho : Fin 7 → Fin k) (K c t j b G F : Fin k) : Formula k :=
  .ex ((label (rho 6).castSucc K.castSucc c.castSucc t.castSucc j.castSucc b.castSucc (Fin.last k)).conj
    (ForcingHS.hs actionFormula (fun i => (rho i).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (K c t j b G F : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (result rho K c t j b G F) ↔
      ∃ name, Label (env (rho 6)) (env K) (env c) (env t) (env j) (env b) name ∧
        ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) name := by
  simp only [result,Formula.Realize,label_semantics (M := M),ForcingHS.hs_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- The actual source label exists and is HS. Its check family, raw name and
singleton support witnesses are constructed inside arbitrary ZF models. -/
def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t j b : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
        (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
          (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
            (.imp (ProjectSyntax.encode id (ForcingNormalFilter.normal I G F))
              (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
                (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
                  (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
                    (.imp (ProjectSyntax.encode id (Formula.mem j I))
                      (ProjectSyntax.encode id (result rho K c t j b G F)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t j b : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w mu G F c t j b)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho I K B w mu G F c t j b)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingNormalFilter.normal_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),result_semantics (M := M),Formula.Realize,Project.Term.eval_bound]
  intro hw hSmall hp hG hNormal hFilter hc ht hj
  obtain ⟨name,hn⟩ := exists_label hM hc (bound (rho 6)) (bound t) (bound j) (bound b)
  exact ⟨name,hn,label_HS hM (fun i => bound (rho i)) hp hG hNormal hFilter hw hSmall hc ht hj hn⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu G F c t j b : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence rho I K B w mu G F c t j b)) :=
  ModelTransfer.derives (fun _ hM => construction_models rho I K B w mu G F c t j b hM)

end PPAC.Migration.ForcingLabelNames
