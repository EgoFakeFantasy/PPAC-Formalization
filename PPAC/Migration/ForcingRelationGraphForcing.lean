/- Fixed TailGraphs.BinaryRelation.mem_graph.
The witnesses remain actual HS names; the graph is the constructed collected set.
No generic filter, external quotient or function is substituted for the graph. -/
import PPAC.Migration.ForcingRelationGraphSupport

namespace PPAC.Migration.ForcingRelationGraphForcing
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces forces)
open ForcingMapConditions (MapRel)
open ForcingHS (HS)
open ForcingOrderedPairName (OrderedPairName)
open ForcingRelationGraphSupport (relation relation_semantics)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Holds {n : Nat} (Q : Formula (n+3)) (env : Fin n → M.Carrier .set)
    (p x y : M.Carrier .set) : Prop :=
  Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
    (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))) Q

def Monotone {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F : M.Carrier .set) : Prop :=
  ∀ p q x y, (Definitional.Project.FirstOrderSemantics.reduct M).mem p P →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    HS A env G P F x → HS A env G P F y → Holds Q env p x y → Holds Q env q x y

def Congruent {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F : M.Carrier .set) : Prop :=
  ∀ p x y x' y', HS A env G P F x → HS A env G P F y →
    HS A env G P F x' → HS A env G P F y' →
    Forces true R env P x x' p → Forces true R env P y y' p →
    (Holds Q env p x y ↔ Holds Q env p x' y')

def DensePairs {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F t X Y nu p : M.Carrier .set) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
    ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
      ∃ x y a, HS A env G P F x ∧ HS A env G P F y ∧ OrderedPairName t x y a ∧
        Forces false R env P x X r ∧ Forces false R env P y Y r ∧ Holds Q env r x y ∧
        Forces true R env P nu a r

theorem mem_graph (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R A : Formula (n+2)) (Q : Formula (n+3)) (env : Fin n → M.Carrier .set)
    (P G F t X Y : Fin n) {name nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env (env P))
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem (env t) (env P))
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env P) → MapRel R env r (env t))
    (hX : HS A env (env G) (env P) (env F) (env X))
    (hY : HS A env (env G) (env P) (env F) (env Y))
    (hmono : Monotone R A Q env (env P) (env G) (env F))
    (hcongr : Congruent R A Q env (env P) (env G) (env F))
    (hgraph : ForcingRelationGraph.Graph R Q env P t X Y name)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env P)) :
    Forces false R env (env P) nu name p ↔
      DensePairs R A Q env (env P) (env G) (env F) (env t) (env X) (env Y) nu p := by
  constructor
  · intro h q hq hqp
    obtain ⟨r,a,c,hr,hrq,hc,he,hrc,heq⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R env (env P) nu name p).mp h).2 q hq hqp
    obtain ⟨_,x,b,y,d,hxe,hye,hpair,hMX,hMY,hQ⟩ :=
      (ForcingRelationGraph.edge_graph hM R Q env P t X Y hgraph a c).mp he
    have hx := ForcingHS.child hX hxe
    have hy := ForcingHS.child hY hye
    exact ⟨r,hr,hrq,x,y,a,hx,hy,hpair,
      ForcingAtomicBasic.mem_mono hM hpre hr hrc hMX,
      ForcingAtomicBasic.mem_mono hM hpre hr hrc hMY,
      hmono c r x y hc hr hrc hx hy hQ,heq⟩
  · intro h
    apply (ForcingAtomicRelations.mem_iff hM R env (env P) nu name p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,x,y,a,hx,hy,ha,hMX,hMY,hQ,he⟩ := h q hq hqp
    obtain ⟨s,sigma,c,hs,hsr,hc,hscEdge,hsc,hxs⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R env (env P) x (env X) r).mp hMX).2 r hr (hpre.1 r hr)
    obtain ⟨v,tau,d,hv,hvs,hd,htdEdge,hvd,hyt⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R env (env P) y (env Y) r).mp hMY).2 s hs hsr
    have hvr := hpre.2 v s r hv hs hr hvs hsr
    have hvc := hpre.2 v s c hv hs hc hvs hsc
    have hxs' := ForcingAtomicBasic.eq_mono hM hpre hv hvs hxs
    have hSigma := ForcingHS.child hX hscEdge
    have hTau := ForcingHS.child hY htdEdge
    obtain ⟨b,hb⟩ := ForcingOrderedPairName.exists_orderedPairName hM (env t) sigma tau
    have hEdge : PureKuratowski.PairMember M b v name :=
      (ForcingRelationGraph.edge_graph hM R Q env P t X Y hgraph b v).mpr
        ⟨hv,sigma,c,tau,d,hscEdge,htdEdge,hb,
          ForcingAtomicBasic.mem_of_edge_eq hM hpre hc hvc hscEdge (ForcingAtomicBasic.eq_refl hM hpre sigma v hv),
          ForcingAtomicBasic.mem_of_edge_eq hM hpre hd hvd htdEdge (ForcingAtomicBasic.eq_refl hM hpre tau v hv),
          (hcongr v x y sigma tau hx hy hSigma hTau hxs' hyt).mp (hmono r v x y hr hv hvr hx hy hQ)⟩
    have he' := ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hv hvr he)
      (ForcingOrderedPairForcing.eq_opair_congr hM hpre ht htop ha hb hxs' hyt)
    exact ⟨v,b,v,hv,hpre.2 v r q hv hr hq hvr hrq,hv,hEdge,hpre.1 v hv,he'⟩


def monotone {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F : Fin m) : Formula m :=
  (Formula.all (Formula.all (Formula.all (Formula.all ((Formula.mem (Fin.last (m+0)).castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)).castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+0)).castSucc.castSucc.castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3))).imp
    ((relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+0)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))).imp
    (relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)))))))))))))

theorem monotone_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (monotone R A Q base P G F) ↔
      Monotone R A Q (fun j => v (base j)) (v P) (v G) (v F) := by
  simp only [monotone,Monotone,Holds,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    
    relation_semantics (M := M),Nat.add_zero,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def congruent {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F : Fin m) : Formula m :=
  (Formula.all (Formula.all (Formula.all (Formula.all (Formula.all ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4))).imp
    ((forces true R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc).imp
    ((forces true R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+4)) (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc).imp
    ((relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc).iff
    (relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+0)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4)))))))))))))))

theorem congruent_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (congruent R A Q base P G F) ↔
      Congruent R A Q (fun j => v (base j)) (v P) (v G) (v F) := by
  simp only [congruent,Congruent,Holds,Source.Formula.iff,Formula.Realize,
    ForcingHS.hs_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),
    relation_semantics (M := M),Nat.add_zero,Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h p x y x' y' hx hy hx' hy' he hf
    exact ⟨(h p x y x' y' hx hy hx' hy' he hf).1,(h p x y x' y' hx hy hx' hy' he hf).2⟩
  · intro h p x y x' y' hx hy hx' hy' he hf
    exact ⟨(h p x y x' y' hx hy hx' hy' he hf).mp,(h p x y x' y' hx hy hx' hy' he hf).mpr⟩

def densePairs {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F t X Y nu p : Fin m) : Formula m :=
  (Formula.all ((Formula.mem (Fin.last (m+0)) (P).castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last (m+0)) (p).castSucc).imp
    (Formula.ex ((Formula.mem (Fin.last (m+1)) (P).castSucc.castSucc).conj
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) (Fin.last (m+0)).castSucc).conj
    (Formula.ex (Formula.ex (Formula.ex ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc).conj
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc).conj
    ((ForcingOrderedPairName.orderedPairName (t).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc (Fin.last (m+4))).conj
    ((forces false R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (X).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc).conj
    ((forces false R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc (Y).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc).conj
    ((relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc (Fin.last (m+3)).castSucc).conj
    (forces true R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (P).castSucc.castSucc.castSucc.castSucc.castSucc (nu).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)) (Fin.last (m+1)).castSucc.castSucc.castSucc))))))))))))))))

theorem densePairs_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F t X Y nu p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (densePairs R A Q base P G F t X Y nu p) ↔
      DensePairs R A Q (fun j => v (base j)) (v P) (v G) (v F) (v t) (v X) (v Y) (v nu) (v p) := by
  simp only [densePairs,DensePairs,Holds,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingOrderedPairName.orderedPairName_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    relation_semantics (M := M),Nat.add_zero,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def membershipSentence {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (P G F t X Y name nu p : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((Formula.mem t P).imp
    ((Formula.all ((Formula.mem (Fin.last n) P.castSucc).imp
      (ReplacementPredicates.rel R (ReplacementPredicates.paramsUp id) (Fin.last n) t.castSucc))).imp
    ((ForcingHS.hs A id G P F X).imp ((ForcingHS.hs A id G P F Y).imp
    ((monotone R A Q id P G F).imp ((congruent R A Q id P G F).imp
    ((ForcingRelationGraph.graph R Q id P t X Y name).imp ((Formula.mem p P).imp
    ((forces false R id P nu name p).iff (densePairs R A Q id P G F t X Y nu p))))))))))).close

theorem membership_models {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (P G F t X Y name nu p : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (membershipSentence R A Q P G F t X Y name nu p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre ht htop hX hY hmono hcongr hgraph hp
  have htop' : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env P) → MapRel R env r (env t) := by
    intro r hr
    let v : Fin (n+1) → M.Carrier .set := Fin.lastCases r env
    have hr' : Formula.Realize (fun a b => M.relInterp .membership (.cons a (.cons b .nil)))
        v (.mem (Fin.last n) P.castSucc) := by
      simpa only [v,Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc,
        Definitional.Project.FirstOrderSemantics.reduct] using hr
    have hrel := (ForcingMapConditions.rel_semantics (M := M) v R
      (ReplacementPredicates.paramsUp (id : Fin n → Fin n)) (Fin.last n) t.castSucc).mp (htop r hr')
    simpa only [v,ReplacementPredicates.paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using hrel
  have h := mem_graph hM R A Q env P G F t X Y
    ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hpre) ht htop'
    ((ForcingHS.hs_semantics (M := M) env A id G P F X).mp hX)
    ((ForcingHS.hs_semantics (M := M) env A id G P F Y).mp hY)
    ((monotone_semantics (M := M) env R A Q id P G F).mp hmono)
    ((congruent_semantics (M := M) env R A Q id P G F).mp hcongr)
    ((ForcingRelationGraph.graph_semantics (M := M) env R Q id P t X Y name).mp hgraph) hp (nu := env nu)
  constructor
  · intro hm
    exact (densePairs_semantics (M := M) env R A Q id P G F t X Y nu p).mpr
      (h.mp ((ForcingAtomicRelations.forces_semantics (M := M) env false R id P nu name p).mp hm))
  · intro hd
    exact (ForcingAtomicRelations.forces_semantics (M := M) env false R id P nu name p).mpr
      (h.mpr ((densePairs_semantics (M := M) env R A Q id P G F t X Y nu p).mp hd))

theorem membership_kernel_certificate {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (P G F t X Y name nu p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (membershipSentence R A Q P G F t X Y name nu p)) :=
  ModelTransfer.derives (fun _ hM => membership_models R A Q P G F t X Y name nu p hM)

def Regular {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P G F : M.Carrier .set) : Prop :=
  ∀ p x y, (Definitional.Project.FirstOrderSemantics.reduct M).mem p P →
    HS A env G P F x → HS A env G P F y →
    (∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p →
      ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ Holds Q env r x y) →
    Holds Q env p x y

theorem pair_mem_graph (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R A : Formula (n+2)) (Q : Formula (n+3)) (env : Fin n → M.Carrier .set)
    (P G F t X Y : Fin n) {name x y a p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env (env P))
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem (env t) (env P))
    (htop : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env P) → MapRel R env r (env t))
    (hX : HS A env (env G) (env P) (env F) (env X))
    (hY : HS A env (env G) (env P) (env F) (env Y))
    (hmono : Monotone R A Q env (env P) (env G) (env F))
    (hcongr : Congruent R A Q env (env P) (env G) (env F))
    (hregular : Regular R A Q env (env P) (env G) (env F))
    (hgraph : ForcingRelationGraph.Graph R Q env P t X Y name)
    (hx : HS A env (env G) (env P) (env F) x) (hy : HS A env (env G) (env P) (env F) y)
    (ha : OrderedPairName (env t) x y a)
    (hp : (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env P)) :
    Forces false R env (env P) a name p ↔
      Forces false R env (env P) x (env X) p ∧ Forces false R env (env P) y (env Y) p ∧ Holds Q env p x y := by
  rw [mem_graph hM R A Q env P G F t X Y hpre ht htop hX hY hmono hcongr hgraph hp]
  constructor
  · intro h
    have hd : ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q (env P) → MapRel R env q p →
        ∃ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env P) ∧ MapRel R env r q ∧
          Forces false R env (env P) x (env X) r ∧ Forces false R env (env P) y (env Y) r ∧ Holds Q env r x y := by
      intro q hq hqp
      obtain ⟨r,hr,hrq,u,v,b,hu,hv,hb,hU,hV,hQ,he⟩ := h q hq hqp
      obtain ⟨hxu,hyv⟩ := (ForcingOrderedPairForcing.eq_opair_iff hM hpre ht htop ha hb).mp he
      exact ⟨r,hr,hrq,(ForcingAtomicLaws.mem_congr_left hM hpre hxu).mpr hU,
        (ForcingAtomicLaws.mem_congr_left hM hpre hyv).mpr hV,
        (hcongr r x y u v hx hy hu hv hxu hyv).mpr hQ⟩
    refine ⟨ForcingAtomicBasic.mem_of_dense hM hpre hp ?_,ForcingAtomicBasic.mem_of_dense hM hpre hp ?_,
      hregular p x y hp hx hy ?_⟩
    · intro q hq hqp
      obtain ⟨r,hr,hrq,hX,_,_⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hX⟩
    · intro q hq hqp
      obtain ⟨r,hr,hrq,_,hY,_⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hY⟩
    · intro q hq hqp
      obtain ⟨r,hr,hrq,_,_,hQ⟩ := hd q hq hqp
      exact ⟨r,hr,hrq,hQ⟩
  · rintro ⟨hMX,hMY,hQ⟩ q hq hqp
    exact ⟨q,hq,hpre.1 q hq,x,y,a,hx,hy,ha,
      ForcingAtomicBasic.mem_mono hM hpre hq hqp hMX,ForcingAtomicBasic.mem_mono hM hpre hq hqp hMY,
      hmono p q x y hp hq hqp hx hy hQ,ForcingAtomicBasic.eq_refl hM hpre a q hq⟩

def regular {n m : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (base : Fin n → Fin m) (P G F : Fin m) : Formula m :=
  (Formula.all (Formula.all (Formula.all ((Formula.mem (Fin.last (m+0)).castSucc.castSucc (P).castSucc.castSucc.castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).imp
    ((ForcingHS.hs A (fun j => (base j).castSucc.castSucc.castSucc) (G).castSucc.castSucc.castSucc (P).castSucc.castSucc.castSucc (F).castSucc.castSucc.castSucc (Fin.last (m+2))).imp
    ((Formula.all ((Formula.mem (Fin.last (m+3)) (P).castSucc.castSucc.castSucc.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc.castSucc) (Fin.last (m+3)) (Fin.last (m+0)).castSucc.castSucc.castSucc).imp
    (Formula.ex ((Formula.mem (Fin.last (m+4)) (P).castSucc.castSucc.castSucc.castSucc.castSucc).conj
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+4)) (Fin.last (m+3)).castSucc).conj
    (relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+4)) (Fin.last (m+1)).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc))))))).imp
    (relation Q (fun j => (base j).castSucc.castSucc.castSucc) (Fin.last (m+0)).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))))))))))

theorem regular_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R A : Formula (n+2)) (Q : Formula (n+3)) (base : Fin n → Fin m) (P G F : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (regular R A Q base P G F) ↔
      Regular R A Q (fun j => v (base j)) (v P) (v G) (v F) := by
  simp only [regular,Regular,Holds,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingHS.hs_semantics (M := M),
    relation_semantics (M := M),Nat.add_zero,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def pairMembershipSentence {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (P G F t X Y name x y a p : Fin n) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder R id P).imp ((Formula.mem t P).imp
    ((Formula.all ((Formula.mem (Fin.last n) P.castSucc).imp
      (ReplacementPredicates.rel R (ReplacementPredicates.paramsUp id) (Fin.last n) t.castSucc))).imp
    ((ForcingHS.hs A id G P F X).imp ((ForcingHS.hs A id G P F Y).imp
    ((monotone R A Q id P G F).imp ((congruent R A Q id P G F).imp ((regular R A Q id P G F).imp
    ((ForcingRelationGraph.graph R Q id P t X Y name).imp
    ((ForcingHS.hs A id G P F x).imp ((ForcingHS.hs A id G P F y).imp
    ((ForcingOrderedPairName.orderedPairName t x y a).imp ((Formula.mem p P).imp
    ((forces false R id P a name p).iff ((forces false R id P x X p).conj
      ((forces false R id P y Y p).conj (relation Q id p x y))))))))))))))) )).close

theorem pairMembership_models {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (P G F t X Y name x y a p : Fin n) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (pairMembershipSentence R A Q P G F t X Y name x y a p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hpre ht htop hX hY hmono hcongr hregular hgraph hx hy ha hp
  have htop' : ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env P) → MapRel R env r (env t) := by
    intro r hr
    let v : Fin (n+1) → M.Carrier .set := Fin.lastCases r env
    have hr' : Formula.Realize (fun a b => M.relInterp .membership (.cons a (.cons b .nil)))
        v (.mem (Fin.last n) P.castSucc) := by
      simpa only [v,Formula.Realize,Fin.lastCases_last,Fin.lastCases_castSucc,
        Definitional.Project.FirstOrderSemantics.reduct] using hr
    have hrel := (ForcingMapConditions.rel_semantics (M := M) v R
      (ReplacementPredicates.paramsUp (id : Fin n → Fin n)) (Fin.last n) t.castSucc).mp (htop r hr')
    simpa only [v,ReplacementPredicates.paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using hrel
  have h := pair_mem_graph hM R A Q env P G F t X Y
    ((ForcingAtomicBasic.preorder_semantics (M := M) env R id P).mp hpre) ht htop'
    ((ForcingHS.hs_semantics (M := M) env A id G P F X).mp hX)
    ((ForcingHS.hs_semantics (M := M) env A id G P F Y).mp hY)
    ((monotone_semantics (M := M) env R A Q id P G F).mp hmono)
    ((congruent_semantics (M := M) env R A Q id P G F).mp hcongr)
    ((regular_semantics (M := M) env R A Q id P G F).mp hregular)
    ((ForcingRelationGraph.graph_semantics (M := M) env R Q id P t X Y name).mp hgraph)
    ((ForcingHS.hs_semantics (M := M) env A id G P F x).mp hx)
    ((ForcingHS.hs_semantics (M := M) env A id G P F y).mp hy)
    ((ForcingOrderedPairName.orderedPairName_semantics (M := M) env t x y a).mp ha) hp
  constructor
  · intro hm
    obtain ⟨hx,hy,hQ⟩ := h.mp ((ForcingAtomicRelations.forces_semantics (M := M) env false R id P a name p).mp hm)
    exact ⟨(ForcingAtomicRelations.forces_semantics (M := M) env false R id P x X p).mpr hx,
      (ForcingAtomicRelations.forces_semantics (M := M) env false R id P y Y p).mpr hy,
      (relation_semantics (M := M) env Q id p x y).mpr hQ⟩
  · rintro ⟨hx,hy,hQ⟩
    exact (ForcingAtomicRelations.forces_semantics (M := M) env false R id P a name p).mpr
      (h.mpr ⟨(ForcingAtomicRelations.forces_semantics (M := M) env false R id P x X p).mp hx,
        (ForcingAtomicRelations.forces_semantics (M := M) env false R id P y Y p).mp hy,
        (relation_semantics (M := M) env Q id p x y).mp hQ⟩)

theorem pairMembership_kernel_certificate {n : Nat} (R A : Formula (n+2)) (Q : Formula (n+3))
    (P G F t X Y name x y a p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (pairMembershipSentence R A Q P G F t X Y name x y a p)) :=
  ModelTransfer.derives (fun _ hM => pairMembership_models R A Q P G F t X Y name x y a p hM)

end PPAC.Migration.ForcingRelationGraphForcing
