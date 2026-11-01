/- Fixed TailGraphs.BinaryRelation.test/graph. This file constructs the actual
raw collected relation graph from the existing product-entry set function.
HS support/transport and forced graph application are separate consumers. -/
import PPAC.Migration.ForcingProductEntries
import PPAC.Migration.ForcingOrderedPairForcing

namespace PPAC.Migration.ForcingRelationGraph
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicRelations (Forces)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Test {n : Nat} (R : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P X Y i p : M.Carrier .set) : Prop :=
  ∃ a b x c y d, PureKuratowski.Code M i a b ∧ PureKuratowski.Code M a x c ∧
    PureKuratowski.Code M b y d ∧ Forces false R env P x X p ∧ Forces false R env P y Y p ∧
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))) Q

def test {n m : Nat} (R : Formula (n+2)) (Q : Formula (n+3))
    (rho : Fin n → Fin m) (P X Y i p : Fin m) : Formula m :=
  .ex (.ex (.ex (.ex (.ex (.ex ((PairSyntax.ordered i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc).conj
    ((PairSyntax.ordered (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc).conj
    ((PairSyntax.ordered (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5))).conj
    ((ForcingAtomicRelations.forces false R (fun j => (rho j).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) P.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj
    ((ForcingAtomicRelations.forces false R (fun j => (rho j).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) P.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc Y.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).conj
    (Q.rename (Fin.lastCases (Fin.last (m+4)).castSucc (Fin.lastCases (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.lastCases p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (fun j => (rho j).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)))))))))))))))

theorem test_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2)) (Q : Formula (n+3))
    (rho : Fin n → Fin m) (P X Y i p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (test R Q rho P X Y i p) ↔
      Test R Q (fun j => v (rho j)) (v P) (v X) (v Y) (v i) (v p) := by
  simp only [test,Test,Formula.Realize,KuratowskiZF.source_code,
    ForcingAtomicRelations.forces_semantics (M := M),DefinableMinimaChoice.realize_rename,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  apply exists_congr; intro a
  apply exists_congr; intro b
  apply exists_congr; intro x
  apply exists_congr; intro c
  apply exists_congr; intro y
  apply exists_congr; intro d
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (and_congr Iff.rfl (and_congr Iff.rfl ?_))))
  have he : (fun j => Fin.lastCases d (Fin.lastCases y (Fin.lastCases c (Fin.lastCases x (Fin.lastCases b (Fin.lastCases a v)))))
      (Fin.lastCases (Fin.last (m+4)).castSucc (Fin.lastCases (Fin.last (m+2)).castSucc.castSucc.castSucc
      (Fin.lastCases p.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        (fun z => (rho z).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))) j)) =
      Fin.lastCases y (Fin.lastCases x (Fin.lastCases (v p) (fun j => v (rho j)))) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
      · refine Fin.lastCases ?_ (fun j => ?_) j <;>
          simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  rw [he]

def testFormula {n : Nat} (R : Formula (n+2)) (Q : Formula (n+3)) (P X Y : Fin n) : Formula (n+2) :=
  test R Q (fun j => j.castSucc.castSucc) P.castSucc.castSucc X.castSucc.castSucc Y.castSucc.castSucc
    (Fin.last n).castSucc (Fin.last (n+1))

theorem testFormula_semantics {n : Nat} (R : Formula (n+2)) (Q : Formula (n+3))
    (env : Fin n → M.Carrier .set) (P X Y : Fin n) (i p : M.Carrier .set) :
    MapRel (testFormula R Q P X Y) env i p ↔ Test R Q env (env P) (env X) (env Y) i p := by
  unfold MapRel testFormula
  rw [test_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

def Graph {n : Nat} (R : Formula (n+2)) (Q : Formula (n+3)) (env : Fin n → M.Carrier .set)
    (P t X Y : Fin n) (name : M.Carrier .set) : Prop :=
  ∃ J f, ForcingCohenCoordinates.Cartesian (env X) (env Y) J ∧ ForcingProductEntries.Graph (env t) J f ∧
    ForcingCollectedName.Collected (testFormula R Q P X Y) env J f (env P) name

def graph {n m : Nat} (R : Formula (n+2)) (Q : Formula (n+3)) (rho : Fin n → Fin m)
    (P t X Y : Fin n) (name : Fin m) : Formula m :=
  .ex (.ex ((ForcingCohenCoordinates.cartesian (rho X).castSucc.castSucc (rho Y).castSucc.castSucc (Fin.last m).castSucc).conj
    ((ForcingProductEntries.graph (rho t).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (ForcingCollectedName.collected (testFormula R Q P X Y) (fun j => (rho j).castSucc.castSucc)
      (Fin.last m).castSucc (Fin.last (m+1)) (rho P).castSucc.castSucc name.castSucc.castSucc))))

theorem graph_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2)) (Q : Formula (n+3))
    (rho : Fin n → Fin m) (P t X Y : Fin n) (name : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (graph R Q rho P t X Y name) ↔
      Graph R Q (fun j => v (rho j)) P t X Y (v name) := by
  simp only [graph,Graph,Formula.Realize,ForcingCohenCoordinates.cartesian_semantics (M := M),
    ForcingProductEntries.graph_semantics (M := M),ForcingCollectedName.collected_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem family_names (hM : FirstOrder.Theory.Models M nativeZF)
    {P t X Y J f : M.Carrier .set} (hX : ForcingNames.IsName P X) (hY : ForcingNames.IsName P Y)
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem t P)
    (hJ : ForcingCohenCoordinates.Cartesian X Y J) (hf : ForcingProductEntries.Graph t J f) :
    ∀ i name, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
      PureKuratowski.PairMember M i name f → ForcingNames.IsName P name := by
  intro i name hi hn
  obtain ⟨a,ha,b,hb,hcode⟩ := (hJ i).mp hi
  obtain ⟨_,a',b',x,p,y,q,hcode',hx,hy,hname⟩ := (hf.2 i name).mp hn
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  exact ForcingOrderedPairName.isName hM hname ht
    (ForcingNames.child_condition hX ⟨a,hx,ha⟩).2 (ForcingNames.child_condition hY ⟨b,hy,hb⟩).2

theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (Q : Formula (n+3)) (env : Fin n → M.Carrier .set) (P t X Y : Fin n)
    (hX : ForcingNames.IsName (env P) (env X)) (hY : ForcingNames.IsName (env P) (env Y))
    (ht : (Definitional.Project.FirstOrderSemantics.reduct M).mem (env t) (env P)) :
    ∃ name, Graph R Q env P t X Y name ∧ ForcingNames.IsName (env P) name := by
  obtain ⟨J,f,hJ,hf⟩ := ForcingProductEntries.construct (t := env t) hM hX hY
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM (testFormula R Q P X Y) env J f (env P)
  exact ⟨name,⟨J,f,hJ,hf,hn⟩,ForcingCollectedName.isName hM hn (family_names hM hX hY ht hJ hf)⟩

theorem edge_graph (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (Q : Formula (n+3)) (env : Fin n → M.Carrier .set) (P t X Y : Fin n)
    {name : M.Carrier .set} (h : Graph R Q env P t X Y name) (child p : M.Carrier .set) :
    PureKuratowski.PairMember M child p name ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env P) ∧ ∃ x c y d,
        PureKuratowski.PairMember M x c (env X) ∧ PureKuratowski.PairMember M y d (env Y) ∧
        ForcingOrderedPairName.OrderedPairName (env t) x y child ∧
        Forces false R env (env P) x (env X) p ∧ Forces false R env (env P) y (env Y) p ∧
        Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
          (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))) Q := by
  obtain ⟨J,f,hJ,hf,hn⟩ := h
  rw [ForcingCollectedName.edge_collected hM hn]
  constructor
  · rintro ⟨hp,i,hi,hic,hR⟩
    obtain ⟨a,ha,b,hb,hcode⟩ := (hJ i).mp hi
    obtain ⟨_,a',b',x,c,y,d,hcode',hx,hy,hname⟩ := (hf.2 i child).mp hic
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    obtain ⟨a',b',x',c',y',d',hcode',hx',hy',hMX,hMY,hQ⟩ :=
      (testFormula_semantics R Q env P X Y i p).mp hR
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hx hx'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hy hy'
    exact ⟨hp,x,c,y,d,⟨a,hx,ha⟩,⟨b,hy,hb⟩,hname,hMX,hMY,hQ⟩
  · rintro ⟨hp,x,c,y,d,⟨a,hx,ha⟩,⟨b,hy,hb⟩,hname,hMX,hMY,hQ⟩
    obtain ⟨i,hcode⟩ := KuratowskiZF.exists_code hM a b
    have hi := (hJ i).mpr ⟨a,ha,b,hb,hcode⟩
    exact ⟨hp,i,hi,(hf.2 i child).mpr ⟨hi,a,b,x,c,y,d,hcode,hx,hy,hname⟩,
      (testFormula_semantics R Q env P X Y i p).mpr ⟨a,b,x,c,y,d,hcode,hx,hy,hMX,hMY,hQ⟩⟩

def constructionSentence {n : Nat} (R : Formula (n+2)) (Q : Formula (n+3)) (P t X Y : Fin n) : Source.Sentence :=
  ((ForcingNames.isName P X).imp ((ForcingNames.isName P Y).imp ((Formula.mem t P).imp
    (.ex ((graph R Q Fin.castSucc P t X Y (Fin.last n)).conj
      (ForcingNames.isName P.castSucc (Fin.last n))))))).close

theorem construction_models {n : Nat} (R : Formula (n+2)) (Q : Formula (n+3)) (P t X Y : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence R Q P t X Y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hX hY ht
  obtain ⟨name,hn,hname⟩ := construct hM R Q env P t X Y
    ((ForcingNames.isName_semantics (M := M) env P X).mp hX)
    ((ForcingNames.isName_semantics (M := M) env P Y).mp hY) ht
  let v : Fin (n+1) → M.Carrier .set := Fin.lastCases name env
  refine ⟨name,?_,?_⟩
  · apply (graph_semantics (M := M) v R Q Fin.castSucc P t X Y (Fin.last n)).mpr
    simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hn
  · apply (ForcingNames.isName_semantics (M := M) v P.castSucc (Fin.last n)).mpr
    simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hname

theorem construction_kernel_certificate {n : Nat} (R : Formula (n+2)) (Q : Formula (n+3)) (P t X Y : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence R Q P t X Y)) :=
  ModelTransfer.derives (fun _ hM => construction_models R Q P t X Y hM)

end PPAC.Migration.ForcingRelationGraph
