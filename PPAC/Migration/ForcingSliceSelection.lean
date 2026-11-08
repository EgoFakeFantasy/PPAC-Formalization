/- Pinned RelationCalculus.UnaryRelation.test/select/select_fixed/mem_select:31-86.
Direct consumer: SliceGeometry.B, Ypart and Spart. Reuse the EXISTING literal
child family and collected-name/HS kernels; no new collection or recursion. -/
import PPAC.Migration.ForcingWellorderedTarget

namespace PPAC.Migration.ForcingSliceSelection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Test {k : Nat} (R Q : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (P X i p : M.Carrier .set) : Prop :=
  ∃ child c, PureKuratowski.Code M i child c ∧ Forces false R env P child X p ∧ MapRel Q env p child

def test {k m : Nat} (R Q : Formula (k+2)) (base : Fin k → Fin m)
    (P X i p : Fin m) : Formula m :=
  let b : Fin k → Fin (m+2) := fun j => (base j).castSucc.castSucc
  let child := (Fin.last m).castSucc
  .ex (.ex ((PairSyntax.ordered i.castSucc.castSucc child (Fin.last (m+1))).conj
    ((ForcingAtomicRelations.forces false R b P.castSucc.castSucc child X.castSucc.castSucc p.castSucc.castSucc).conj
      (ReplacementPredicates.rel Q b p.castSucc.castSucc child))))

theorem test_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (R Q : Formula (k+2))
    (base : Fin k → Fin m) (P X i p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (test R Q base P X i p) ↔
      Test R Q (fun j => v (base j)) (v P) (v X) (v i) (v p) := by
  simp only [test,Test,Formula.Realize,KuratowskiZF.source_code,ForcingAtomicRelations.forces_semantics,
    ForcingMapConditions.rel_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def testFormula {k : Nat} (R Q : Formula (k+2)) (P X : Fin k) : Formula (k+2) :=
  test R Q (fun j => j.castSucc.castSucc) P.castSucc.castSucc X.castSucc.castSucc
    (Fin.last k).castSucc (Fin.last (k+1))

theorem testFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (R Q : Formula (k+2))
    (P X : Fin k) (i p : M.Carrier .set) :
    MapRel (testFormula R Q P X) env i p ↔ Test R Q env (env P) (env X) i p := by
  unfold MapRel testFormula
  rw [test_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

/-- Exact literal-child edge equation of the source selection. -/
def Selected {k : Nat} (R Q : Formula (k+2)) (env : Fin k → M.Carrier .set)
    (P X name : M.Carrier .set) : Prop :=
  ∀ child p, PureKuratowski.PairMember M child p name ↔
    (∃ c, PureKuratowski.PairMember M child c X) ∧
      (Project.FirstOrderSemantics.reduct M).mem p P ∧ Forces false R env P child X p ∧ MapRel Q env p child

theorem edge_selected (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R Q : Formula (k+2)} {env : Fin k → M.Carrier .set} {P X : Fin k} {f name : M.Carrier .set}
    (hf : ForcingSeparation.Family (env X) f)
    (hn : ForcingCollectedName.Collected (testFormula R Q P X) env (env X) f (env P) name) :
    Selected R Q env (env P) (env X) name := by
  intro child p
  rw [ForcingCollectedName.edge_collected hM hn]
  constructor
  · rintro ⟨hp,i,hi,hic,ht⟩
    obtain ⟨_,c,hcode⟩ := (hf i child).mp hic
    obtain ⟨other,d,hcode',hm,hq⟩ := (testFormula_semantics env R Q P X i p).mp ht
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact ⟨⟨c,i,hcode,hi⟩,hp,hm,hq⟩
  · rintro ⟨⟨c,i,hcode,hi⟩,hp,hm,hq⟩
    exact ⟨hp,i,hi,(hf i child).mpr ⟨hi,c,hcode⟩,
      (testFormula_semantics env R Q P X i p).mpr ⟨child,c,hcode,hm,hq⟩⟩

/-- Source select and select_fixed, using the same actual support. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (Q : Formula (k+2)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S mul X : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hFixX : Supported (fun j => env (rho j)) (env S) (env X))
    (hMove : ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi (env S) → ∀ act,
      MapRel actionFormula (fun j => env (rho j)) pi act → ∀ p q x x',
      (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) → PureKuratowski.PairMember M p q act →
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x →
      ForcingStabilizer.Action (env (rho 6)) act x x' → MapRel Q env p x → MapRel Q env q x') :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Supported (fun j => env (rho j)) (env S) name ∧
      Selected (orderFormula (rho 0) mul) Q env (env (rho 6)) (env X) name := by
  let R := orderFormula (rho 0) mul
  let T := testFormula R Q (rho 6) X
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  obtain ⟨f,hf⟩ := ForcingSeparation.exists_family hM (env X)
  have hFamily : ForcingCollectedHS.FamilyHS v7 (env G) (env (rho 6)) (env F) (env X) f := by
    intro i child _ hic
    obtain ⟨hi,c,hcode⟩ := (hf i child).mp hic
    exact ForcingHS.child hX ⟨i,hcode,hi⟩
  have hPerm : ForcingCollectedHS.Permutes T env v7 (env S) (env X) f (env (rho 6)) := by
    intro pi hpi act hAct child p image q had him hpq
    obtain ⟨hp,i,hi,hic,hTest⟩ := had
    obtain ⟨hiX,c,hcode⟩ := (hf i child).mp hic
    obtain ⟨other,d,hcode',hm,hq⟩ := (testFormula_semantics env R Q (rho 6) X i p).mp hTest
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    have ha := (mapRel_action v7 pi act).mp hAct
    have hPermAct := ForcingProductFamily.action_permutation ha
    obtain ⟨image',c',he',him',_⟩ := ForcingSeparation.entry_permute hM hPermAct.1
      (ForcingHS.isName hX) (hFixX pi hpi act hAct) ⟨i,hcode,hiX⟩
    have heq := ForcingNameConjugacy.unique hM hPermAct.1 him' him
    subst image'
    obtain ⟨j,hcodeJ,hj⟩ := he'
    have hMem := (ForcingSeparation.symmetry hM env rho G F mul hPres hG hF
      ((hG pi).mp (hS.1 pi hpi)) hAct (.mem (0 : Fin 2) 1) (args2 child (env X)) (args2 image (env X))
      (fun a => Fin.cases him (Fin.cases (hFixX pi hpi act hAct) (fun b => Fin.elim0 b)) a) hp hpq).mp hm
    exact ⟨hPermAct.1.2 p q hpq,j,hj,(hf j image).mpr ⟨hj,c',hcodeJ⟩,
      (testFormula_semantics env R Q (rho 6) X j q).mpr
        ⟨image,c',hcodeJ,hMem,hMove pi hpi act hAct p q child image hp hpq (ForcingHS.child hX ⟨i,hcode,hiX⟩) him hq⟩⟩
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM T env (env X) f (env (rho 6))
  exact ⟨name,ForcingCollectedHS.collect_HS hM T env v7 hPres hG hF hS hSF hFamily hPerm hn,
    fun pi hpi act hAct => ForcingCollectedHS.fixed hM T env v7 hPres hG hS hFamily hPerm hn hpi hAct,
    edge_selected hM hf hn⟩

/-- Pinned mem_select, with all source regularity laws made explicit. -/
theorem mem_selected (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R Q : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P X name nu p : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hName : Selected R Q env P X name)
    (hChild : ∀ child c, PureKuratowski.PairMember M child c X → Predicate H env child)
    (hNu : Predicate H env nu)
    (hMono : ∀ a b x, (Project.FirstOrderSemantics.reduct M).mem a P →
      (Project.FirstOrderSemantics.reduct M).mem b P → MapRel R env b a → Predicate H env x →
      MapRel Q env a x → MapRel Q env b x)
    (hCongr : ∀ a x y, Predicate H env x → Predicate H env y → Forces true R env P x y a →
      (MapRel Q env a x ↔ MapRel Q env a y))
    (hRegular : ∀ a x, (Project.FirstOrderSemantics.reduct M).mem a P → Predicate H env x →
      (∀ b, (Project.FirstOrderSemantics.reduct M).mem b P → MapRel R env b a →
        ∃ c, (Project.FirstOrderSemantics.reduct M).mem c P ∧ MapRel R env c b ∧ MapRel Q env c x) → MapRel Q env a x)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P nu name p ↔ Forces false R env P nu X p ∧ MapRel Q env p nu := by
  constructor
  · intro h
    have hd : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
        ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
          Forces false R env P nu X r ∧ MapRel Q env r nu := by
      intro q hq hqp
      obtain ⟨r,child,c,hr,hrq,hc,he,hrc,heq⟩ := ((ForcingAtomicRelations.mem_iff hM R env P nu name p).mp h).2 q hq hqp
      obtain ⟨⟨d,heX⟩,_,hm,hRel⟩ := (hName child c).mp he
      exact ⟨r,hr,hrq,(ForcingAtomicLaws.mem_congr_left hM hpre heq).mpr
        (ForcingAtomicBasic.mem_mono hM hpre hr hrc hm),
        (hCongr r nu child hNu (hChild child d heX) heq).mpr (hMono c r child hc hr hrc (hChild child d heX) hRel)⟩
    exact ⟨ForcingAtomicBasic.mem_of_dense hM hpre hp (fun q hq hqp => by
      obtain ⟨r,hr,hrq,hm,_⟩ := hd q hq hqp; exact ⟨r,hr,hrq,hm⟩),
      hRegular p nu hp hNu (fun q hq hqp => by
        obtain ⟨r,hr,hrq,_,hRel⟩ := hd q hq hqp; exact ⟨r,hr,hrq,hRel⟩)⟩
  · rintro ⟨hm,hRel⟩
    apply (ForcingAtomicRelations.mem_iff hM R env P nu name p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,child,c,hr,hrq,hc,he,hrc,heq⟩ := ((ForcingAtomicRelations.mem_iff hM R env P nu X p).mp hm).2 q hq hqp
    have hMem := ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hrc he (ForcingAtomicBasic.eq_refl hM hpre child r hr)
    have hRel' := (hCongr r nu child hNu (hChild child c he) heq).mp
      (hMono p r nu hp hr (hpre.2 r q p hr hq hp hrq hqp) hNu hRel)
    exact ⟨r,child,r,hr,hrq,hr,(hName child r).mpr ⟨⟨c,he⟩,hr,hMem,hRel'⟩,hpre.1 r hr,heq⟩

/-- Reuse the existing class_unique raw-edge extensionality proof verbatim.
This is literal equality of genuine names, needed for internal parameter
functionality; forced equality alone would not suffice. -/
theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R Q : Formula (k+2)} {env : Fin k → M.Carrier .set}
    {P X name name' : M.Carrier .set}
    (hn : ForcingNames.IsName P name) (hn' : ForcingNames.IsName P name')
    (hc : Selected R Q env P X name) (hc' : Selected R Q env P X name') : name = name'  := by
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


def selected {k m : Nat} (R Q : Formula (k+2)) (base : Fin k → Fin m)
    (P X name : Fin m) : Formula m :=
  let b : Fin k → Fin (m+2) := fun j => (base j).castSucc.castSucc
  let child := (Fin.last m).castSucc
  let p := Fin.last (m+1)
  .all (.all ((Source.SetLanguage.edge name.castSucc.castSucc child p).iff
    ((Formula.ex (Source.SetLanguage.edge X.castSucc.castSucc.castSucc child.castSucc (Fin.last (m+2)))).conj
      ((Formula.mem p P.castSucc.castSucc).conj
        ((ForcingAtomicRelations.forces false R b P.castSucc.castSucc child X.castSucc.castSucc p).conj
          (ReplacementPredicates.rel Q b p child))))))

theorem selected_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (R Q : Formula (k+2))
    (base : Fin k → Fin m) (P X name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (selected R Q base P X name) ↔
      Selected R Q (fun j => v (base j)) (v P) (v X) (v name) := by
  simp only [selected,Selected,Source.Formula.iff,Formula.Realize,KuratowskiZF.source_edge,
    ForcingAtomicRelations.forces_semantics,ForcingMapConditions.rel_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x p => ⟨(h x p).1,(h x p).2⟩,fun h x p => ⟨(h x p).mp,(h x p).mpr⟩⟩

/-- The existing binary movement formula already quotes unary movement:
its second name is ignored. No new action or movement syntax is introduced. -/
theorem lifted_semantics {k : Nat} (env : Fin k → M.Carrier .set) (Q : Formula (k+2))
    (p x y : M.Carrier .set) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))) (Q.rename Fin.castSucc) ↔ MapRel Q env p x := by
  rw [DefinableMinimaChoice.realize_rename]
  simp only [Fin.lastCases_castSucc]
  rfl

theorem construct_from_moves (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (Q : Formula (k+2)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S mul X : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hFixX : Supported (fun j => env (rho j)) (env S) (env X))
    (hMoves : ForcingRelationGraphSupport.Moves (Q.rename Fin.castSucc) env rho G F S) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Supported (fun j => env (rho j)) (env S) name ∧
      Selected (orderFormula (rho 0) mul) Q env (env (rho 6)) (env X) name := by
  apply construct hM Q env rho I K B w G F S mul X hPres hG hF hS hSF hX hFixX
  intro pi hpi act hAct p q x x' hp hpq hx hxx hQ
  exact (lifted_semantics env Q q x' x').mp
    (hMoves pi hpi act hAct p q x x x' x' hp hpq hx hx hxx hxx
      ((lifted_semantics env Q p x x).mpr hQ))

def resultFormula {k : Nat} (Q : Formula (k+2)) (rho : Fin 7 → Fin k) (G F S mul X : Fin k) : Formula k :=
  .ex ((ForcingHS.hs actionFormula (fun j => (rho j).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).conj
    ((ForcingEquivariantMix.fixedAll (fun j => (rho j).castSucc) S.castSucc (Fin.last k)).conj
      (selected (orderFormula (rho 0) mul) Q Fin.castSucc (rho 6).castSucc X.castSucc (Fin.last k))))

theorem resultFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (Q : Formula (k+2))
    (rho : Fin 7 → Fin k) (G F S mul X : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (resultFormula Q rho G F S mul X) ↔
      ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
        Supported (fun j => env (rho j)) (env S) name ∧
        Selected (orderFormula (rho 0) mul) Q env (env (rho 6)) (env X) name := by
  simp only [resultFormula,Formula.Realize,ForcingHS.hs_semantics,ForcingEquivariantMix.fixedAll_semantics,
    selected_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def sentence {k : Nat} (Q : Formula (k+2)) (rho : Fin 7 → Fin k)
    (I K B w G F S mul X : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S X),
      ProjectSyntax.encode id (ForcingRelationGraphSupport.moves (Q.rename Fin.castSucc) id rho G F S)].foldr
      Definitional.Formula.imp (ProjectSyntax.encode id (resultFormula Q rho G F S mul X)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k : Nat} (Q : Formula (k+2)) (rho : Fin 7 → Fin k)
    (I K B w G F S mul X : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence Q rho I K B w G F S mul X)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingHS.hs_semantics,ForcingEquivariantMix.fixedAll_semantics,ForcingRelationGraphSupport.moves_semantics,
    resultFormula_semantics,id_eq]
  exact construct_from_moves hM Q env rho I K B w G F S mul X

theorem kernel_certificate {k : Nat} (Q : Formula (k+2)) (rho : Fin 7 → Fin k)
    (I K B w G F S mul X : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence Q rho I K B w G F S mul X)) :=
  ModelTransfer.derives (fun _ hM => models Q rho I K B w G F S mul X hM)

end PPAC.Migration.ForcingSliceSelection
