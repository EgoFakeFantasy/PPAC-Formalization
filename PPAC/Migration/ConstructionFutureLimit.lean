/- Pinned CellReorder.future_cut, isSuccLimit branch. Construct its actual
internal interval and restricted families from the existing native ZF APIs;
consume Timeline continuity and the already proved directed-union square.
No external WellFounded, host max, or choice of a family of witnesses. -/
import PPAC.Migration.ConstructionFutureCut

namespace PPAC.Migration.ConstructionFutureLimit
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFirstAppearance (Timeline Cover At)
open ConstructionFutureFamily (Cuts Suprema Products CutAt)
open ConstructionRealCuts (Subset)
open ForcingConditionGraphs (FunctionOn function_input function_unique)
open ConstructionDirectedSystem (IndexLaws)
open ConstructionBlockStages (MonotoneImages)
open ConstructionSubobjectUnion (Union)
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square)
open ConstructionConservativeHull (Closure)
open ConstructionCellRestriction (Stages)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Interval (I R a b K : M.Carrier .set) : Prop := ∀ i,
  (Project.FirstOrderSemantics.reduct M).mem i K ↔
    (Project.FirstOrderSemantics.reduct M).mem i I ∧
    (a = i ∨ PureKuratowski.PairMember M a i R) ∧ PureKuratowski.PairMember M i b R

def ClosedOrder (K R E : M.Carrier .set) : Prop := ∀ i j,
  PureKuratowski.PairMember M i j E ↔
    (Project.FirstOrderSemantics.reduct M).mem i K ∧
    (Project.FirstOrderSemantics.reduct M).mem j K ∧ (i = j ∨ PureKuratowski.PairMember M i j R)

def intervalMember {m : Nat} (R a b i : Fin m) : Project.Formula 1 m :=
  .conj (.disj (Project.Formula.extensionalEq (.bound a) (.bound i))
    (ProjectSyntax.encode id (Source.SetLanguage.edge R a i)))
    (ProjectSyntax.encode id (Source.SetLanguage.edge R i b))

theorem intervalMember_freeClosed {m : Nat} (R a b i : Fin m) : (intervalMember R a b i).FreeClosed := by
  simp -implicitDefEqProofs [intervalMember,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ProjectSyntax.freeClosed]

theorem intervalMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R a b i : Fin m) :
    Project.Formula.satisfies env (intervalMember R a b i) ↔
      (env.bound a = env.bound i ∨ PureKuratowski.PairMember M (env.bound a) (env.bound i) (env.bound R)) ∧
        PureKuratowski.PairMember M (env.bound i) (env.bound b) (env.bound R) := by
  simp only [intervalMember,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def closedLe {m : Nat} (R i j : Fin m) : Project.Formula 1 m :=
  .disj (Project.Formula.extensionalEq (.bound i) (.bound j))
    (ProjectSyntax.encode id (Source.SetLanguage.edge R i j))

theorem closedLe_freeClosed {m : Nat} (R i j : Fin m) : (closedLe R i j).FreeClosed := by
  simp -implicitDefEqProofs [closedLe,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ProjectSyntax.freeClosed]

theorem closedLe_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R i j : Fin m) :
    Project.Formula.satisfies env (closedLe R i j) ↔
      env.bound i = env.bound j ∨ PureKuratowski.PairMember M (env.bound i) (env.bound j) (env.bound R) := by
  simp only [closedLe,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem exists_interval (hM : FirstOrder.Theory.Models M nativeZF) (I R a b : M.Carrier .set) :
    ∃ K, Interval I R a b K := by
  let schema : Project.UnarySchema 3 := {body := intervalMember 1 2 3 0,freeClosed := intervalMember_freeClosed ..}
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases R (Fin.cases a (fun _ => b)),free := fun _ => I}
  obtain ⟨K,hK⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env I
  exact ⟨K,fun i => (hK i).trans (and_congr_right fun _ => intervalMember_semantics hM (env.push i) 1 2 3 0)⟩

theorem exists_order (hM : FirstOrder.Theory.Models M nativeZF) (K R : M.Carrier .set) :
    ∃ E, ClosedOrder K R E := by
  let schema : Project.BinarySchema 1 := {body := closedLe 2 1 0,freeClosed := closedLe_freeClosed ..}
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {bound := fun _ => R,free := fun _ => K}
  obtain ⟨E,_,hE⟩ := ZF.exists_setRelationOn_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env K
  exact ⟨E,fun i j => (hE i j).trans (and_congr_right fun _ => and_congr_right fun _ =>
    closedLe_semantics hM ((env.push i).push j) 2 1 0)⟩

theorem index_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {V I R bottom S a b K E : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hK : Interval I R a b K) (hE : ClosedOrder K R E) : IndexLaws K E := by
  refine ⟨fun i hi => (hE i i).mpr ⟨hi,hi,Or.inl rfl⟩,?_,?_⟩
  · intro i j k hi hj hk hij hjk
    apply (hE i k).mpr
    refine ⟨hi,hk,?_⟩
    rcases ((hE i j).mp hij).2.2 with he | hij'
    · subst j; exact ((hE i k).mp hjk).2.2
    · rcases ((hE j k).mp hjk).2.2 with he | hjk'
      · subst k; exact Or.inr hij'
      · exact Or.inr (hT.1.linear.2.1.2 i ((hK i).mp hi).1 j ((hK j).mp hj).1 k ((hK k).mp hk).1 hij' hjk')
  · intro i j hi hj
    rcases hT.1.linear.2.2 i ((hK i).mp hi).1 j ((hK j).mp hj).1 with he | hij | hji
    · have heq := (ModelTransfer.extensionality hM).eq_of_same_members i j he
      exact ⟨j,hj,(hE i j).mpr ⟨hi,hj,Or.inl heq⟩,(hE j j).mpr ⟨hj,hj,Or.inl rfl⟩⟩
    · exact ⟨j,hj,(hE i j).mpr ⟨hi,hj,Or.inr hij⟩,(hE j j).mpr ⟨hj,hj,Or.inl rfl⟩⟩
    · exact ⟨i,hi,(hE i i).mpr ⟨hi,hi,Or.inl rfl⟩,(hE j i).mpr ⟨hj,hi,Or.inr hji⟩⟩

/-- The original function graph restricted by the native restriction API. -/
def Restricted (K F f : M.Carrier .set) : Prop := FunctionOn K f ∧ ∀ i x,
  PureKuratowski.PairMember M i x f ↔ (Project.FirstOrderSemantics.reduct M).mem i K ∧ PureKuratowski.PairMember M i x F

theorem restrict_family (hM : FirstOrder.Theory.Models M nativeZF)
    {I K F : M.Carrier .set} (hF : FunctionOn I F) (hKI : Subset K I) : ∃ f, Restricted K F f := by
  obtain ⟨f,hf⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) F K
  refine ⟨f,⟨?_,?_⟩,hf.2⟩
  · intro z hz
    obtain ⟨i,x,hix⟩ := hf.1 z hz
    exact ⟨i,x,((hf.2 i x).mp ⟨z,hix,hz⟩).1,hix⟩
  · intro i hi
    obtain ⟨x,hix,_⟩ := hF.2 i (hKI i hi)
    exact ⟨x,(hf.2 i x).mpr ⟨hi,hix⟩,fun y hiy => function_unique hF ((hf.2 i y).mp hiy).2 hix⟩

theorem restrict_cuts {I K retained S CutsGraph cuts : M.Carrier .set}
    (hKI : Subset K I) (hCuts : Cuts I retained S CutsGraph) (hRestrict : Restricted K CutsGraph cuts) :
    Cuts K retained S cuts := by
  refine ⟨hRestrict.1,fun i x => (hRestrict.2 i x).trans ?_⟩
  exact ⟨fun h => ⟨h.1,((hCuts.2 i x).mp h.2).2⟩,
    fun h => ⟨h.1,(hCuts.2 i x).mpr ⟨hKI i h.1,h.2⟩⟩⟩

theorem restrict_products {I K GV Domains Muls domains muls : M.Carrier .set}
    (hKI : Subset K I) (hP : Products I GV Domains Muls)
    (hD : Restricted K Domains domains) (hG : Restricted K Muls muls) : Products K GV domains muls := by
  refine ⟨hG.1,?_⟩
  intro i G
  constructor
  · intro hiG
    obtain ⟨hi,hiG⟩ := (hG.2 i G).mp hiG
    obtain ⟨D,hiD,hDG⟩ := ((hP.2 i G).mp hiG).2
    exact ⟨hi,D,(hD.2 i D).mpr ⟨hi,hiD⟩,hDG⟩
  · rintro ⟨hi,D,hiD,hDG⟩
    exact (hG.2 i G).mpr ⟨hi,(hP.2 i G).mpr ⟨hKI i hi,D,((hD.2 i D).mp hiD).2,hDG⟩⟩

theorem restrict_mono {I R K E F f : M.Carrier .set}
    (hKI : Subset K I) (hE : ClosedOrder K R E) (hF : FunctionOn I F)
    (hMono : MonotoneImages I R F) (hf : Restricted K F f) : MonotoneImages K E f := by
  intro i j A B hi hj hij hiA hjB
  have hiA' := ((hf.2 i A).mp hiA).2
  have hjB' := ((hf.2 j B).mp hjB).2
  rcases ((hE i j).mp hij).2.2 with he | hij'
  · subst j
    have hAB := function_unique hF hiA' hjB'
    exact fun x hx => hAB ▸ hx
  · exact hMono i j A B (hKI i hi) (hKI j hj) hij' hiA' hjB'

theorem timeline_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {V I R bottom S : M.Carrier .set} (hT : Timeline hM V I R bottom S) : MonotoneImages I R S := by
  intro i j A B _ _ hij hiA hjB x hx
  obtain ⟨D,hD,hxD⟩ := hT.2.2.2.2.2.1 i j x (Or.inr hij) ⟨A,hiA,hx⟩
  exact (function_unique hT.2.1 hD hjB) ▸ hxD

/-- The source max(a,j) argument, using the actual internal linear order.
Timeline continuity is used at the supplied limit; no external supremum. -/
theorem cut_union (hM : FirstOrder.Theory.Models M nativeZF)
    {V I R bottom S retained a b K cuts B : M.Carrier .set}
    (hT : Timeline hM V I R bottom S) (hK : Interval I R a b K)
    (hCuts : Cuts K retained S cuts) (hB : CutAt retained S b B)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a I)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b I)
    (hab : PureKuratowski.PairMember M a b R) (hnb : b ≠ bottom)
    (hLimit : ¬ ∃ i, Cover I R i b) : Union K cuts B := by
  obtain ⟨Db,hDb,hB⟩ := hB
  intro x
  constructor
  · intro hx
    obtain ⟨hxRet,hxDb⟩ := (hB x).mp hx
    obtain ⟨j,hj,hjb,hxj⟩ := hT.2.2.2.2.2.2.2 b hb hnb hLimit x ⟨Db,hDb,hxDb⟩
    have place : ∀ k, (Project.FirstOrderSemantics.reduct M).mem k I →
        (a = k ∨ PureKuratowski.PairMember M a k R) → PureKuratowski.PairMember M k b R → At S k x →
        ∃ k C, (Project.FirstOrderSemantics.reduct M).mem k K ∧
          PureKuratowski.PairMember M k C cuts ∧ (Project.FirstOrderSemantics.reduct M).mem x C := by
      intro k hk hak hkb hxk
      have hkK := (hK k).mpr ⟨hk,hak,hkb⟩
      obtain ⟨C,hC,_⟩ := hCuts.1.2 k hkK
      obtain ⟨D,hD,hCut⟩ := ((hCuts.2 k C).mp hC).2
      obtain ⟨E,hE,hxE⟩ := hxk
      exact ⟨k,C,hkK,hC,(hCut x).mpr ⟨hxRet,(function_unique hT.2.1 hE hD) ▸ hxE⟩⟩
    rcases hT.1.linear.2.2 a ha j hj with he | haj | hja
    · exact place j hj (Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members a j he)) hjb hxj
    · exact place j hj (Or.inr haj) hjb hxj
    · exact place a ha (Or.inl rfl) hab (hT.2.2.2.2.2.1 j a x (Or.inr hja) hxj)
  · rintro ⟨i,C,hi,hiC,hxC⟩
    obtain ⟨D,hD,hCut⟩ := ((hCuts.2 i C).mp hiC).2
    obtain ⟨hxRet,hxD⟩ := (hCut x).mp hxC
    obtain ⟨E,hE,hxE⟩ := hT.2.2.2.2.2.1 i b x (Or.inr ((hK i).mp hi).2.2) ⟨D,hD,hxD⟩
    exact (hB x).mpr ⟨hxRet,(function_unique hT.2.1 hE hDb) ▸ hxE⟩

/-- Exactly the earlier induction hypotheses on a <= i < b, for the SAME
supremum family. No local future at b is assumed. -/
def EarlierSquares (V GV e I R a b CutsGraph Futures A C GA GC ia ic : M.Carrier .set) : Prop :=
  ∀ i B D, (Project.FirstOrderSemantics.reduct M).mem i I →
    (a = i ∨ PureKuratowski.PairMember M a i R) → PureKuratowski.PairMember M i b R →
    PureKuratowski.PairMember M i B CutsGraph → PureKuratowski.PairMember M i D Futures →
    ∃ PB PD GB GD ib idD, Base V GV e B PB GB ib ∧ Base V GV e D PD GD idD ∧
      Square A B C D GA GB GC GD e ia ib ic

/-- Full source limit branch with its actual internal interval, restricted
families and cut continuity discharged. Only the strict earlier induction
hypotheses remain; the supplied ordinary-supremum value at b gains its
conservative Base and full Square. -/
theorem limit (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls
      A C PA PC GA GC ia ic B F : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hT : Timeline hM V I R bottom S) (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hA : Base V GV e A PA GA ia) (hC : Base V GV e C PC GC ic)
    (hCuts : Cuts I retained S CutsGraph) (hFuture : Suprema I V GV e C CutsGraph Futures)
    (hCM : Products I GV CutsGraph CutMuls) (hFM : Products I GV Futures FutureMuls)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a I)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b I)
    (hab : PureKuratowski.PairMember M a b R) (hnb : b ≠ bottom)
    (hLimit : ¬ ∃ i, Cover I R i b)
    (hEarlier : EarlierSquares V GV e I R a b CutsGraph Futures A C GA GC ia ic)
    (hbB : PureKuratowski.PairMember M b B CutsGraph) (hbF : PureKuratowski.PairMember M b F Futures) :
    ∃ PB GB ib PF GF iF, Base V GV e B PB GB ib ∧ Base V GV e F PF GF iF ∧
      ConstructionIntermediate.Sup V GV e C B F ∧ Square A B C F GA GB GC GF e ia ib ic := by
  obtain ⟨K,hK⟩ := exists_interval hM I R a b
  obtain ⟨E,hE⟩ := exists_order hM K R
  have hKI : Subset K I := fun i hi => ((hK i).mp hi).1
  have hNonempty := (hK a).mpr ⟨ha,Or.inl rfl,hab⟩
  obtain ⟨cuts,hCutsR⟩ := restrict_family hM hCuts.1 hKI
  obtain ⟨futures,hFutureR⟩ := restrict_family hM hFuture.1 hKI
  obtain ⟨cutMuls,hCMR⟩ := restrict_family hM hCM.1 hKI
  obtain ⟨futureMuls,hFMR⟩ := restrict_family hM hFM.1 hKI
  have hCutsK := restrict_cuts hKI hCuts hCutsR
  have hCMK := restrict_products hKI hCM hCutsR hCMR
  have hFMK := restrict_products hKI hFM hFutureR hFMR
  have hMono := ConstructionFutureFamily.cuts_mono hCuts (timeline_mono hM hT)
  have hCutsMono := restrict_mono hKI hE hCuts.1 hMono hCutsR
  have hFutureMono := restrict_mono hKI hE hFuture.1 (ConstructionFutureFamily.suprema_mono hFuture hMono) hFutureR
  have hLocal : ConstructionFutureCut.LocalSquares V GV e K cuts futures A C GA GC ia ic := by
    intro i Bi Fi hi hiB hiF
    obtain ⟨hiI,hai,hib⟩ := (hK i).mp hi
    exact hEarlier i Bi Fi hiI hai hib ((hCutsR.2 i Bi).mp hiB).2 ((hFutureR.2 i Fi).mp hiF).2
  have hCutB := ((hCuts.2 b B).mp hbB).2
  have hUnion := cut_union hM hT hK hCutsK hCutB ha hb hab hnb hLimit
  obtain ⟨PB,GB,ib,hBaseB⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ
    (ConstructionFutureFamily.cut_closed hStages hRet hCutB)
  obtain ⟨D,PD,GD,idD,hBaseD,_,hSupD,hSquare⟩ := ConstructionFutureCut.limit hM hv hc hJ
    (index_laws hM hT hK hE) ⟨a,hNonempty⟩ hCutsR.1 hFutureR.1 hCMK hFMK
    hCutsMono hFutureMono hLocal hUnion hA hBaseB hC
  obtain ⟨B',hbB',hSupF⟩ := ((hFuture.2 b F).mp hbF).2
  have hEqB := function_unique hCuts.1 hbB' hbB
  subst B'
  have hEqF := ConstructionFutureFamily.sup_unique hM hSupD hSupF
  subst D
  exact ⟨PB,GB,ib,PD,GD,idD,hBaseB,hBaseD,hSupF,hSquare⟩

def earlierSquaresFormula {m : Nat} (V GV e I R a b CutsGraph Futures A C GA GC ia ic : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound I.succ.succ.succ)) (.imp (closedLe R.succ.succ.succ a.succ.succ.succ 2) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ 2 b.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge CutsGraph.succ.succ.succ 2 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Futures.succ.succ.succ 2 0)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 5 3 1) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 4 2 0) (ConstructionUnionPushout.square A.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 C.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 GA.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 GC.succ.succ.succ.succ.succ.succ.succ.succ.succ 2 e.succ.succ.succ.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 ic.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))

theorem earlierSquaresFormula_freeClosed {m : Nat} (V GV e I R a b CutsGraph Futures A C GA GC ia ic : Fin m) :
    (earlierSquaresFormula V GV e I R a b CutsGraph Futures A C GA GC ia ic).FreeClosed := by
  simp -implicitDefEqProofs [earlierSquaresFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    closedLe_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed]

theorem earlierSquaresFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V GV e I R a b CutsGraph Futures A C GA GC ia ic : Fin m) :
    Project.Formula.satisfies env (earlierSquaresFormula V GV e I R a b CutsGraph Futures A C GA GC ia ic) ↔ EarlierSquares (env.bound V) (env.bound GV) (env.bound e) (env.bound I) (env.bound R) (env.bound a) (env.bound b) (env.bound CutsGraph) (env.bound Futures) (env.bound A) (env.bound C) (env.bound GA) (env.bound GC) (env.bound ia) (env.bound ic) := by
  simp only [earlierSquaresFormula,EarlierSquares,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    closedLe_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM]
  rfl

/-- Native pure-membership certificate for the source's actual limit case. -/
def limitSentence {m : Nat} (V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls A C PA PC GA GC ia ic B F : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp (ConstructionFutureFamily.cutsFormula I retained S CutsGraph) (.imp (ConstructionFutureFamily.supremaFormula I V GV e C CutsGraph Futures) (.imp (ConstructionFutureFamily.productsFormula I GV CutsGraph CutMuls) (.imp (ConstructionFutureFamily.productsFormula I GV Futures FutureMuls) (.imp (.mem (.bound a) (.bound I)) (.imp (.mem (.bound b) (.bound I)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge R a b)) (.imp (.neg (Project.Formula.extensionalEq (.bound b) (.bound bottom))) (.imp (.neg (.existsE (ConstructionFirstAppearance.cover I.succ R.succ 0 b.succ))) (.imp (earlierSquaresFormula V GV e I R a b CutsGraph Futures A C GA GC ia ic) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge CutsGraph b B)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Futures b F)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ 5 4 3) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ 2 1 0) (.conj (ConstructionIntermediate.sup V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ) (ConstructionUnionPushout.square A.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ GA.succ.succ.succ.succ.succ.succ 4 GC.succ.succ.succ.succ.succ.succ 1 e.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ 3 ic.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.extensionalEq,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionFirstAppearance.timeline_freeClosed,ConstructionCellRestriction.stages_freeClosed,
      ConstructionConservativeHull.closure_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,
      ConstructionFutureFamily.cutsFormula_freeClosed,ConstructionFutureFamily.supremaFormula_freeClosed,
      ConstructionFutureFamily.productsFormula_freeClosed,ConstructionFirstAppearance.cover_freeClosed,
      earlierSquaresFormula_freeClosed,ConstructionIntermediate.sup_freeClosed,ConstructionUnionPushout.square_freeClosed]

theorem limit_models {m : Nat} (V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls A C PA PC GA GC ia ic B F : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (limitSentence V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls A C PA PC GA GC ia ic B F)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (limitSentence V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls A C PA PC GA GC ia ic B F)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,
    ConstructionCellRestriction.stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,
    ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionFutureFamily.cutsFormula_semantics hM,
    ConstructionFutureFamily.supremaFormula_semantics hM,ConstructionFutureFamily.productsFormula_semantics hM,
    ConstructionFirstAppearance.cover_semantics hM,earlierSquaresFormula_semantics hM,
    ConstructionIntermediate.sup_semantics hM,ConstructionUnionPushout.square_semantics hM]
  exact limit hM

theorem limit_kernel_certificate {m : Nat} (V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls A C PA PC GA GC ia ic B F : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (limitSentence V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls A C PA PC GA GC ia ic B F)) :=
  ModelTransfer.derives (fun _ hM => limit_models V GV e I R bottom S retained a b CutsGraph Futures CutMuls FutureMuls A C PA PC GA GC ia ic B F hM)

end PPAC.Migration.ConstructionFutureLimit
