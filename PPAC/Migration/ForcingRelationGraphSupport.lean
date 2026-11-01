/- Fixed TailGraphs.BinaryRelation.test_permute/graph/graph_fixed.
Derive actual entry permutation from parent fixedness and relation invariance,
then consume the existing collector HS/fixed theorems. -/
import PPAC.Migration.ForcingRelationGraph
import PPAC.Migration.ForcingRelationClassMove

namespace PPAC.Migration.ForcingRelationGraphSupport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open Source.SetLanguage (args2)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingStabilizer (Action)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Move {k : Nat} (Q : Formula (k+3)) (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F : Fin k) (a : M.Carrier .set) : Prop :=
  ∀ p q x y x' y', (Definitional.Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
    PureKuratowski.PairMember M p q a →
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) x →
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) y →
    Action (env (rho 6)) a x x' → Action (env (rho 6)) a y y' →
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))) Q →
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases y' (Fin.lastCases x' (Fin.lastCases q env))) Q

def Moves {k : Nat} (Q : Formula (k+3)) (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F H : Fin k) : Prop :=
  ∀ g, (Definitional.Project.FirstOrderSemantics.reduct M).mem g (env H) → ∀ a,
    MapRel actionFormula (fun j => env (rho j)) g a → Move Q env rho G F a

def relation {k m : Nat} (Q : Formula (k+3)) (base : Fin k → Fin m) (p x y : Fin m) : Formula m :=
  Q.rename (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p base)))

theorem relation_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (Q : Formula (k+3))
    (base : Fin k → Fin m) (p x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (relation Q base p x y) ↔
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases (v y) (Fin.lastCases (v x) (Fin.lastCases (v p) (fun j => v (base j))))) Q := by
  unfold relation
  rw [DefinableMinimaChoice.realize_rename]
  have he : (fun j => v (Fin.lastCases y (Fin.lastCases x (Fin.lastCases p base)) j)) =
      Fin.lastCases (v y) (Fin.lastCases (v x) (Fin.lastCases (v p) (fun j => v (base j)))) := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
      · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  rw [he]

def move {k m : Nat} (Q : Formula (k+3)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin k) (G F : Fin k) (a : Fin m) : Formula m :=
  .all (.all (.all (.all (.all (.all ((Formula.mem (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (base (rho 6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc).imp ((Source.SetLanguage.edge a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc).imp ((ForcingHS.hs actionFormula (fun j => (base (rho j)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (base G).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (base (rho 6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (base F).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc).imp ((ForcingHS.hs actionFormula (fun j => (base (rho j)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (base G).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (base (rho 6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (base F).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc).imp ((ForcingStabilizer.action (base (rho 6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc).imp ((ForcingStabilizer.action (base (rho 6)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc (Fin.last (m+5))).imp ((relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc).imp (relation Q (fun j => (base j).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc (Fin.last (m+5)))))))))))))))

theorem move_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (Q : Formula (k+3))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin k) (G F : Fin k) (a : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (move Q base rho G F a) ↔
      Move Q (fun j => v (base j)) rho G F (v a) := by
  simp only [move,Move,Formula.Realize,KuratowskiZF.source_edge,
    ForcingHS.hs_semantics (M := M),ForcingStabilizer.action_semantics (M := M),relation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def moves {k m : Nat} (Q : Formula (k+3)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin k) (G F H : Fin k) : Formula m :=
  .all ((Formula.mem (Fin.last m) (base H).castSucc).imp (.all
    ((ReplacementPredicates.rel actionFormula (fun j => (base (rho j)).castSucc.castSucc)
      (Fin.last m).castSucc (Fin.last (m+1))).imp
      (move Q (fun j => (base j).castSucc.castSucc) rho G F (Fin.last (m+1))))))

theorem moves_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (Q : Formula (k+3))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin k) (G F H : Fin k) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (moves Q base rho G F H) ↔
      Moves Q (fun j => v (base j)) rho G F H := by
  simp only [moves,Moves,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),move_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem move_entries (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (Q : Formula (k+3)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul t X Y : Fin k) {pi a J f : M.Carrier .set}
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation (env I) pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi a)
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hfixX : Action (env (rho 6)) a (env X) (env X))
    (hfixY : Action (env (rho 6)) a (env Y) (env Y))
    (hmove : Move Q env rho G F a)
    (hJ : ForcingCohenCoordinates.Cartesian (env X) (env Y) J)
    (hf : ForcingProductEntries.Graph (env t) J f) :
    ForcingCollectedHS.MoveEntries (ForcingRelationGraph.testFormula (orderFormula (rho 0) mul) Q (rho 6) X Y)
      env J f (env (rho 6)) a := by
  intro child p image q had him hpq
  obtain ⟨hpW,i,hi,hic,hTest⟩ := had
  obtain ⟨a0,ha0,b0,hb0,hcode⟩ := (hJ i).mp hi
  obtain ⟨_,a1,b1,x,c,y,d,hcode',hx,hy,hpair⟩ := (hf.2 i child).mp hic
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  obtain ⟨a1,b1,x1,c1,y1,d1,hcode',hx1,hy1,hMX,hMY,hQ⟩ :=
    (ForcingRelationGraph.testFormula_semantics (orderFormula (rho 0) mul) Q env (rho 6) X Y i p).mp hTest
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hx hx1
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hy hy1
  have har := ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp ha)
  obtain ⟨x',c',heX,hx',_⟩ := ForcingSeparation.entry_permute hM har.1 (ForcingHS.isName hX) hfixX ⟨a0,hx,ha0⟩
  obtain ⟨y',d',heY,hy',_⟩ := ForcingSeparation.entry_permute hM har.1 (ForcingHS.isName hY) hfixY ⟨b0,hy,hb0⟩
  have hfn := ForcingConditionAction.act_function (args2 (env (rho 6)) a) (0 : Fin 2) 1 har.1
  have htW := (hp.2.2.2.2.2 (env t)).mpr (Or.inl ht)
  have htAct := (ForcingConditionAction.relation_semantics (args2 (env (rho 6)) a) (0 : Fin 2) 1 (env t) (env t)).mpr
    (Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht ((mapRel_action _ _ _).mp ha)⟩)
  have hpair' := ForcingOrderedPairName.map_orderedPairName hM hfn hpair htAct hx' hy' him
  have hMX' := (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha (.mem (0 : Fin 2) 1)
    (args2 x (env X)) (args2 x' (env X))
    (fun j => Fin.cases hx' (fun j => Fin.cases hfixX (fun j => Fin.elim0 j) j) j) hpW hpq).mp hMX
  have hMY' := (ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha (.mem (0 : Fin 2) 1)
    (args2 y (env Y)) (args2 y' (env Y))
    (fun j => Fin.cases hy' (fun j => Fin.cases hfixY (fun j => Fin.elim0 j) j) j) hpW hpq).mp hMY
  have hQ' := hmove p q x y x' y' hpW hpq (ForcingHS.child hX ⟨a0,hx,ha0⟩)
    (ForcingHS.child hY ⟨b0,hy,hb0⟩) hx' hy' hQ
  obtain ⟨a',hxa,ha'⟩ := heX
  obtain ⟨b',hyb,hb'⟩ := heY
  obtain ⟨j,hjcode⟩ := KuratowskiZF.exists_code hM a' b'
  have hj := (hJ j).mpr ⟨a',ha',b',hb',hjcode⟩
  exact ⟨har.1.2 p q hpq,j,hj,(hf.2 j image).mpr ⟨hj,a',b',x',c',y',d',hjcode,hxa,hyb,hpair'⟩,
    (ForcingRelationGraph.testFormula_semantics (orderFormula (rho 0) mul) Q env (rho 6) X Y j q).mpr
      ⟨a',b',x',c',y',d',hjcode,hxa,hyb,hMX',hMY',hQ'⟩⟩

theorem permutes (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (Q : Formula (k+3)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F H mul t X Y : Fin k)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup (env I) (env G) (env H))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hfixX : Supported (fun j => env (rho j)) (env H) (env X))
    (hfixY : Supported (fun j => env (rho j)) (env H) (env Y))
    (hmove : Moves Q env rho G F H)
    {J f : M.Carrier .set} (hJ : ForcingCohenCoordinates.Cartesian (env X) (env Y) J)
    (hf : ForcingProductEntries.Graph (env t) J f) :
    ForcingCollectedHS.Permutes (ForcingRelationGraph.testFormula (orderFormula (rho 0) mul) Q (rho 6) X Y)
      env (fun j => env (rho j)) (env H) J f (env (rho 6)) := by
  intro g hg a ha
  exact move_entries hM Q env rho I K B w G F mul t X Y hp hG hF
    ((hG g).mp (hH.1 g hg)) ha ht hX hY (hfixX g hg a ha) (hfixY g hg a ha)
    (hmove g hg a ha) hJ hf

theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (Q : Formula (k+3)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F H mul t X Y : Fin k)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hH : ForcingConjugationGraph.Subgroup (env I) (env G) (env H))
    (ht : ForcingWithTopCarrier.Empty (env t))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hfixX : Supported (fun j => env (rho j)) (env H) (env X))
    (hfixY : Supported (fun j => env (rho j)) (env H) (env Y))
    (hmove : Moves Q env rho G F H)
    (hHF : (Definitional.Project.FirstOrderSemantics.reduct M).mem (env H) (env F)) :
    ∃ name, ForcingRelationGraph.Graph (orderFormula (rho 0) mul) Q env (rho 6) t X Y name ∧
      HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Supported (fun j => env (rho j)) (env H) name := by
  obtain ⟨J,f,hJ,hf⟩ := ForcingProductEntries.construct (t := env t) hM (ForcingHS.isName hX) (ForcingHS.isName hY)
  let R := ForcingRelationGraph.testFormula (orderFormula (rho 0) mul) Q (rho 6) X Y
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM R env J f (env (rho 6))
  have hfamily := ForcingProductEntries.family_hs hM (fun j => env (rho j)) hp hG hF ht hX hY hJ hf
  have hperm := permutes hM Q env rho I K B w G F H mul t X Y hp hG hF hH ht hX hY hfixX hfixY hmove hJ hf
  refine ⟨name,⟨J,f,hJ,hf,hn⟩,
    ForcingCollectedHS.collect_HS hM R env (fun j => env (rho j)) hp hG hF hH hHF hfamily hperm hn,?_⟩
  intro g hg a ha
  exact ForcingCollectedHS.fixed hM R env (fun j => env (rho j)) hp hG hH hfamily hperm hn hg ha

def constructionSentence {k : Nat} (Q : Formula (k+3)) (rho : Fin 7 → Fin k)
    (I K B w G F H mul t X Y : Fin k) : Source.Sentence :=
  ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
    ((ForcingLabelPermutations.carrier I G).imp
    ((ForcingNormalFilter.normal I G F).imp
    ((ForcingConjugationGraph.subgroup I G H).imp
    ((ForcingWithTopCarrier.empty t).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F X).imp
    ((ForcingHS.hs actionFormula rho G (rho 6) F Y).imp
    ((ForcingEquivariantMix.fixedAll rho H X).imp
    ((ForcingEquivariantMix.fixedAll rho H Y).imp
    ((moves Q id rho G F H).imp
    ((Formula.mem H F).imp
    (Formula.ex ((ForcingRelationGraph.graph (orderFormula (rho 0) mul) Q Fin.castSucc (rho 6) t X Y (Fin.last k)).conj
    ((ForcingHS.hs actionFormula (fun j => (rho j).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).conj
      (ForcingEquivariantMix.fixedAll (fun j => (rho j).castSucc) H.castSucc (Fin.last k)))))))))))))))).close

theorem construction_models {k : Nat} (Q : Formula (k+3)) (rho : Fin 7 → Fin k)
    (I K B w G F H mul t X Y : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (constructionSentence Q rho I K B w G F H mul t X Y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hp hG hF hH ht hX hY hfixX hfixY hmove hHF
  obtain ⟨name,hn,hHS,hSupport⟩ := construct hM Q env rho I K B w G F H mul t X Y
    ((ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp)
    ((ForcingLabelPermutations.carrier_semantics (M := M) env I G).mp hG)
    ((ForcingNormalFilter.normal_semantics (M := M) env I G F).mp hF)
    ((ForcingConjugationGraph.subgroup_semantics (M := M) env I G H).mp hH)
    ((ForcingWithTopCarrier.empty_semantics (M := M) env t).mp ht)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F X).mp hX)
    ((ForcingHS.hs_semantics (M := M) env actionFormula rho G (rho 6) F Y).mp hY)
    ((ForcingSupportedNames.supported_semantics (M := M) env rho H X).mp hfixX)
    ((ForcingSupportedNames.supported_semantics (M := M) env rho H Y).mp hfixY)
    ((moves_semantics (M := M) env Q id rho G F H).mp hmove) hHF
  let v : Fin (k+1) → M.Carrier .set := Fin.lastCases name env
  refine ⟨name,?_,?_,?_⟩
  · apply (ForcingRelationGraph.graph_semantics (M := M) v (orderFormula (rho 0) mul) Q Fin.castSucc (rho 6) t X Y (Fin.last k)).mpr
    simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hn
  · apply (ForcingHS.hs_semantics (M := M) v actionFormula (fun j => (rho j).castSucc) G.castSucc (rho 6).castSucc F.castSucc (Fin.last k)).mpr
    simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hHS
  · apply (ForcingSupportedNames.supported_semantics (M := M) v (fun j => (rho j).castSucc) H.castSucc (Fin.last k)).mpr
    simpa only [v,Fin.lastCases_last,Fin.lastCases_castSucc] using hSupport

theorem construction_kernel_certificate {k : Nat} (Q : Formula (k+3)) (rho : Fin 7 → Fin k)
    (I K B w G F H mul t X Y : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (constructionSentence Q rho I K B w G F H mul t X Y)) :=
  ModelTransfer.derives (fun _ hM => construction_models Q rho I K B w G F H mul t X Y hM)

end PPAC.Migration.ForcingRelationGraphSupport
