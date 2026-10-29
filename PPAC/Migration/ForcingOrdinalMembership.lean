/- Pinned OrdinalCodes.mem_selectedRank/mem_selectionType and their
selected-member/initial-segment consequences. Uses the SAME actual rank
function, original dense atomic forcing, and internal set-coded indices. -/
import PPAC.Migration.ForcingOrdinalFixed
import PPAC.Migration.ForcingPowerName

namespace PPAC.Migration.ForcingOrdinalMembership
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ReplacementPredicates (paramsUp rel)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces forces)
open ForcingAtomicBasic (PreorderOn)
open ForcingCollectedName (Collected)
open ForcingOrdinalRanks (Ranks)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The predecessor restriction is present exactly for rank membership. -/
def Before (initial : Bool) (order a b : M.Carrier .set) : Prop :=
  if initial then PureKuratowski.PairMember M b a order else True

def before {m : Nat} (initial : Bool) (order a b : Fin m) : Formula m :=
  if initial then Source.SetLanguage.edge order b a else .equal b b

theorem before_semantics {m : Nat} (env : Fin m → M.Carrier .set)
    (initial : Bool) (order a b : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (before initial order a b) ↔
      Before initial (env order) (env a) (env b) := by
  cases initial <;> simp only [before,Before,Bool.false_eq_true,ite_false,ite_true,
    Formula.Realize,KuratowskiZF.source_edge,eq_self]

/-- Dense selected predecessor witnesses, retaining actual graph values. -/
def Dense {k n : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → M.Carrier .set)
    (R : Formula (n+2)) (rp : Fin n → M.Carrier .set) (P X order history a nu p : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L lp q p →
    ∃ r b c child, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L lp r q ∧
      (Project.FirstOrderSemantics.reduct M).mem b X ∧ Before initial order a b ∧
      (Project.FirstOrderSemantics.reduct M).mem c P ∧ PureKuratowski.PairMember M b child history ∧
      MapRel R rp b c ∧ MapRel L lp r c ∧ Forces true L lp P nu child r

theorem rank_edges (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {rp : Fin n → M.Carrier .set} {P X order history a name : M.Carrier .set}
    (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (han : PureKuratowski.PairMember M a name history) (child c : M.Carrier .set) :
    PureKuratowski.PairMember M child c name ↔
      (Project.FirstOrderSemantics.reduct M).mem c P ∧ ∃ b,
        (Project.FirstOrderSemantics.reduct M).mem b X ∧ Before true order a b ∧
        PureKuratowski.PairMember M b child history ∧ MapRel R rp b c := by
  obtain ⟨J,hJ⟩ := ZF.exists_wellOrderPredecessorSet (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) order X a
  have hc := ForcingOrdinalFixed.rank_collected hM hRanks ha han hJ
  rw [ForcingCollectedName.edge_collected hM hc child c]
  constructor
  · rintro ⟨hp,b,hb,hbc,hR⟩
    exact ⟨hp,b,((hJ b).mp hb).1,((hJ b).mp hb).2,hbc,hR⟩
  · rintro ⟨hp,b,hb,hba,hbc,hR⟩
    exact ⟨hp,b,(hJ b).mpr ⟨hb,hba⟩,hbc,hR⟩

theorem mem_of_edges (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (initial : Bool) (L : Formula (k+2)) (lp : Fin k → M.Carrier .set)
    (R : Formula (n+2)) (rp : Fin n → M.Carrier .set)
    {P X order history a name nu p : M.Carrier .set}
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hEdges : ∀ child c, PureKuratowski.PairMember M child c name ↔
      (Project.FirstOrderSemantics.reduct M).mem c P ∧ ∃ b,
        (Project.FirstOrderSemantics.reduct M).mem b X ∧ Before initial order a b ∧
        PureKuratowski.PairMember M b child history ∧ MapRel R rp b c) :
    Forces false L lp P nu name p ↔ Dense initial L lp R rp P X order history a nu p := by
  rw [ForcingAtomicRelations.mem_iff hM]
  constructor
  · intro h q hq hqp
    obtain ⟨r,child,c,hr,hrq,hc,he,hrc,heq⟩ := h.2 q hq hqp
    obtain ⟨_,b,hb,hba,hbc,hR⟩ := (hEdges child c).mp he
    exact ⟨r,b,c,child,hr,hrq,hb,hba,hc,hbc,hR,hrc,heq⟩
  · intro h
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,b,c,child,hr,hrq,hb,hba,hc,hbc,hR,hrc,heq⟩ := h q hq hqp
    exact ⟨r,child,c,hr,hrq,hc,(hEdges child c).mpr ⟨hc,b,hb,hba,hbc,hR⟩,hrc,heq⟩

theorem mem_selectedRank (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (L : Formula (k+2)) (lp : Fin k → M.Carrier .set) (R : Formula (n+2)) (rp : Fin n → M.Carrier .set)
    {P X order history a name nu p : M.Carrier .set}
    (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (han : PureKuratowski.PairMember M a name history)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false L lp P nu name p ↔ Dense true L lp R rp P X order history a nu p :=
  mem_of_edges hM true L lp R rp hp (rank_edges hM hRanks ha han)

theorem mem_selectionType (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (L : Formula (k+2)) (lp : Fin k → M.Carrier .set) (R : Formula (n+2)) (rp : Fin n → M.Carrier .set)
    {P X order history a name nu p : M.Carrier .set}
    (hn : Collected R rp X history P name)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false L lp P nu name p ↔ Dense false L lp R rp P X order history a nu p := by
  apply mem_of_edges hM false L lp R rp hp
  intro child c
  rw [ForcingCollectedName.edge_collected hM hn child c]
  simp only [ForcingCollectedName.Admissible,Before,Bool.false_eq_true,ite_false,true_and]

theorem selectedRank_mem_selectionType (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {lp : Fin k → M.Carrier .set} {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X history selection a name p : M.Carrier .set}
    (hpre : PreorderOn L lp P) (hn : Collected R rp X history P selection)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (han : PureKuratowski.PairMember M a name history)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hR : MapRel R rp a p) :
    Forces false L lp P name selection p :=
  ForcingAtomicBasic.mem_of_edge_eq hM hpre hp (hpre.1 p hp)
    ((ForcingCollectedName.edge_collected hM hn name p).mpr ⟨hp,a,ha,han,hR⟩)
    (ForcingAtomicBasic.eq_refl hM hpre name p hp)

theorem selectedRank_mem_selectedRank (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {lp : Fin k → M.Carrier .set} {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history a b na nb p : M.Carrier .set}
    (hpre : PreorderOn L lp P) (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X) (hb : (Project.FirstOrderSemantics.reduct M).mem b X)
    (hna : PureKuratowski.PairMember M a na history) (hnb : PureKuratowski.PairMember M b nb history)
    (hab : PureKuratowski.PairMember M a b order)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hR : MapRel R rp a p) :
    Forces false L lp P na nb p :=
  ForcingAtomicBasic.mem_of_edge_eq hM hpre hp (hpre.1 p hp)
    ((rank_edges hM hRanks hb hnb na p).mpr ⟨hp,a,ha,hab,hna,hR⟩)
    (ForcingAtomicBasic.eq_refl hM hpre na p hp)

def dense {k n m : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a nu p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let q := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let r := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let b := (Fin.last (m+2)).castSucc.castSucc
  let c := (Fin.last (m+3)).castSucc
  let child := Fin.last (m+4)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((rel L (paramsUp lp) (Fin.last m) p.castSucc).imp (.ex (.ex (.ex (.ex
      ((Formula.mem r (up P)).conj ((rel L (fun i => up (lp i)) r q).conj
      ((Formula.mem b (up X)).conj ((before initial (up order) (up a) b).conj
      ((Formula.mem c (up P)).conj ((Source.SetLanguage.edge (up history) b child).conj
      ((rel R (fun i => up (rp i)) b c).conj ((rel L (fun i => up (lp i)) r c).conj
      (forces true L (fun i => up (lp i)) (up P) (up nu) child r)))))))))))))))

theorem dense_semantics {k n m : Nat} (env : Fin m → M.Carrier .set)
    (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a nu p : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (dense initial L lp R rp P X order history a nu p) ↔
    Dense initial L (fun i => env (lp i)) R (fun i => env (rp i))
      (env P) (env X) (env order) (env history) (env a) (env nu) (env p) := by
  simp only [dense,Dense,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    before_semantics (M := M),KuratowskiZF.source_edge,ForcingAtomicRelations.forces_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def specification {n m : Nat} (initial : Bool) (R : Formula (n+2)) (rp : Fin n → Fin m)
    (P X order history a name : Fin m) : Formula m :=
  if initial then (ForcingOrdinalRanks.ranks R rp X order P history).conj
    ((Formula.mem a X).conj (Source.SetLanguage.edge history a name))
  else ForcingCollectedName.collected R rp X history P name

theorem specification_semantics {n m : Nat} (env : Fin m → M.Carrier .set)
    (initial : Bool) (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (specification initial R rp P X order history a name) ↔
    if initial then Ranks R (fun i => env (rp i)) (env X) (env order) (env P) (env history) ∧
      (Project.FirstOrderSemantics.reduct M).mem (env a) (env X) ∧
      PureKuratowski.PairMember M (env a) (env name) (env history)
    else Collected R (fun i => env (rp i)) (env X) (env history) (env P) (env name) := by
  cases initial <;> simp only [specification,Bool.false_eq_true,ite_false,ite_true,
    Formula.Realize,ForcingOrdinalRanks.ranks_semantics (M := M),
    ForcingCollectedName.collected_semantics (M := M),KuratowskiZF.source_edge]

def membershipSentence {k n m : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name nu p : Fin m) : Source.Sentence :=
  ((specification initial R rp P X order history a name).imp ((Formula.mem p P).imp
    ((forces false L lp P nu name p).iff (dense initial L lp R rp P X order history a nu p)))).close

theorem membership_models {k n m : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name nu p : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (membershipSentence initial L lp R rp P X order history a name nu p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hs hp
  have hs' := (specification_semantics (M := M) env initial R rp P X order history a name).mp hs
  have hm : Forces false L (fun i => env (lp i)) (env P) (env nu) (env name) (env p) ↔
      Dense initial L (fun i => env (lp i)) R (fun i => env (rp i))
        (env P) (env X) (env order) (env history) (env a) (env nu) (env p) := by
    cases initial with
    | false => exact mem_selectionType hM L _ R _ hs' hp
    | true => exact mem_selectedRank hM L _ R _ hs'.1 hs'.2.1 hs'.2.2 hp
  have hf := ForcingAtomicRelations.forces_semantics (M := M) env false L lp P nu name p
  have hd := dense_semantics (M := M) env initial L lp R rp P X order history a nu p
  exact ⟨fun h => hd.mpr (hm.mp (hf.mp h)),fun h => hf.mpr (hm.mpr (hd.mp h))⟩

theorem membership_kernel_certificate {k n m : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name nu p : Fin m) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (membershipSentence initial L lp R rp P X order history a name nu p)) :=
  ModelTransfer.derives (fun _ hM => membership_models initial L lp R rp P X order history a name nu p hM)

def selectedSentence {k n m : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name b child p : Fin m) : Source.Sentence :=
  ((specification initial R rp P X order history a name).imp
    ((ForcingAtomicBasic.preorder L lp P).imp ((Formula.mem b X).imp
      ((before initial order a b).imp ((Source.SetLanguage.edge history b child).imp
        ((Formula.mem p P).imp ((rel R rp b p).imp (forces false L lp P child name p)))))))).close

theorem selected_models {k n m : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name b child p : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (selectedSentence initial L lp R rp P X order history a name b child p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hs hpre hb hba hbc hp hR
  have hs' := (specification_semantics (M := M) env initial R rp P X order history a name).mp hs
  have hpre' := (ForcingAtomicBasic.preorder_semantics (M := M) env L lp P).mp hpre
  have hba' := (before_semantics (M := M) env initial order a b).mp hba
  have hbc' := (KuratowskiZF.source_edge env history b child).mp hbc
  have hR' := (ForcingMapConditions.rel_semantics (M := M) env R rp b p).mp hR
  apply (ForcingAtomicRelations.forces_semantics (M := M) env false L lp P child name p).mpr
  cases initial with
  | false => exact selectedRank_mem_selectionType hM hpre' hs' hb hbc' hp hR'
  | true => exact selectedRank_mem_selectedRank hM hpre' hs'.1 hb hs'.2.1 hbc' hs'.2.2 hba' hp hR'

theorem selected_kernel_certificate {k n m : Nat} (initial : Bool) (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a name b child p : Fin m) :
    FirstOrder.Derives nativeZF []
      (Translation.sentence (selectedSentence initial L lp R rp P X order history a name b child p)) :=
  ModelTransfer.derives (fun _ hM => selected_models initial L lp R rp P X order history a name b child p hM)

/-- Source initial-segment inclusion, already for every internal candidate name. -/
theorem rank_inclusion (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {lp : Fin k → M.Carrier .set} {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history a b na nb nu p : M.Carrier .set}
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X) (hb : (Project.FirstOrderSemantics.reduct M).mem b X)
    (hna : PureKuratowski.PairMember M a na history) (hnb : PureKuratowski.PairMember M b nb history)
    (hab : a = b ∨ PureKuratowski.PairMember M a b order)
    (hm : Forces false L lp P nu na p) : Forces false L lp P nu nb p := by
  rcases hab with hab | hab
  · subst b
    have hn := ForcingConditionGraphs.function_unique hRanks.1 hna hnb
    exact hn ▸ hm
  · have hp := ForcingAtomicBasic.condition hM hm
    apply (mem_selectedRank hM L lp R rp hRanks hb hnb hp).mpr
    intro q hq hqp
    obtain ⟨r,c,d,child,hr,hrq,hc,hca,hd,hcc,hR,hrd,heq⟩ :=
      (mem_selectedRank hM L lp R rp hRanks ha hna hp).mp hm q hq hqp
    exact ⟨r,c,d,child,hr,hrq,hc,hOrder.trans hc ha hb hca hab,hd,hcc,hR,hrd,heq⟩

theorem type_inclusion (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {lp : Fin k → M.Carrier .set} {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history a na selection nu p : M.Carrier .set}
    (hRanks : Ranks R rp X order P history) (hs : Collected R rp X history P selection)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (hna : PureKuratowski.PairMember M a na history)
    (hm : Forces false L lp P nu na p) : Forces false L lp P nu selection p := by
  have hp := ForcingAtomicBasic.condition hM hm
  apply (mem_selectionType hM L lp R rp (order := order) (a := a) hs hp).mpr
  intro q hq hqp
  obtain ⟨r,c,d,child,hr,hrq,hc,_,hd,hcc,hR,hrd,heq⟩ :=
    (mem_selectedRank hM L lp R rp hRanks ha hna hp).mp hm q hq hqp
  exact ⟨r,c,d,child,hr,hrq,hc,True.intro,hd,hcc,hR,hrd,heq⟩

/-- Exact existing source SubsetF interface, with an arbitrary name-domain formula. -/
theorem selectedRank_subset (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history a b na nb p : M.Carrier .set}
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder
      (KuratowskiZF.interpretation hM) order X)
    (hRanks : Ranks R rp X order P history)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X) (hb : (Project.FirstOrderSemantics.reduct M).mem b X)
    (hna : PureKuratowski.PairMember M a na history) (hnb : PureKuratowski.PairMember M b nb history)
    (hab : a = b ∨ PureKuratowski.PairMember M a b order) : ForcingPowerName.SubsetF L H lp P p na nb :=
  fun _ _ _ _ _ hm => rank_inclusion hM hOrder hRanks ha hb hna hnb hab hm

theorem selectedRank_subset_selectionType (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    {L : Formula (k+2)} {H : Formula (k+1)} {lp : Fin k → M.Carrier .set}
    {R : Formula (n+2)} {rp : Fin n → M.Carrier .set}
    {P X order history a na selection p : M.Carrier .set}
    (hRanks : Ranks R rp X order P history) (hs : Collected R rp X history P selection)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a X)
    (hna : PureKuratowski.PairMember M a na history) : ForcingPowerName.SubsetF L H lp P p na selection :=
  fun _ _ _ _ _ hm => type_inclusion hM hRanks hs ha hna hm

def inclusionBody {k n m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a b na nb selection nu p : Fin m) : Formula m :=
  (ForcingOrdinalRanks.ranks R rp X order P history).imp
    ((ForcingCollectedName.collected R rp X history P selection).imp
      ((Formula.mem a X).imp ((Formula.mem b X).imp
        ((Source.SetLanguage.edge history a na).imp ((Source.SetLanguage.edge history b nb).imp
          (((Formula.equal a b).disj (Source.SetLanguage.edge order a b)).imp
            (((forces false L lp P nu na p).imp (forces false L lp P nu nb p)).conj
              ((forces false L lp P nu na p).imp (forces false L lp P nu selection p)))))))))

/-- All-candidate membership inclusion implies the original unrestricted-HS subset clause. -/
def inclusionSentence {k n m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a b na nb selection nu p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp
    (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound X))
    (ProjectSyntax.encode id (inclusionBody L lp R rp P X order history a b na nb selection nu p)))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem inclusion_models {k n m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a b na nb selection nu p : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (inclusionSentence L lp R rp P X order history a b na nb selection nu p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),inclusionBody,Formula.Realize,
    ForcingOrdinalRanks.ranks_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    KuratowskiZF.source_edge,ForcingAtomicRelations.forces_semantics (M := M)]
  intro hOrder hRanks hs ha hb hna hnb hab
  exact ⟨fun hm => rank_inclusion hM hOrder hRanks ha hb hna hnb hab hm,
    fun hm => type_inclusion hM hRanks hs ha hna hm⟩

theorem inclusion_kernel_certificate {k n m : Nat} (L : Formula (k+2)) (lp : Fin k → Fin m)
    (R : Formula (n+2)) (rp : Fin n → Fin m) (P X order history a b na nb selection nu p : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (inclusionSentence L lp R rp P X order history a b na nb selection nu p)) :=
  ModelTransfer.derives (fun _ hM => inclusion_models L lp R rp P X order history a b na nb selection nu p hM)

end PPAC.Migration.ForcingOrdinalMembership
