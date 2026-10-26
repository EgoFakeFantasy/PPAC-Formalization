/- Pinned ProbeMargins.Path.letterFloor and its order bounds (lines 48-68).
The actual floor graph is constructed inside arbitrary nativeZF models by
existing Separation, bounded cut union and definable function construction.
Consumer: exists_letter_interval / heightIntervals, then extensionHeightCost.
The old height graph's positivity and monotonicity remain source premises. -/
import PPAC.Migration.ConstructionRealCuts
import PPAC.Migration.ConstructionProbeCones

namespace PPAC.Migration.ConstructionProbeLetterFloor
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionProbeAlphabet (InCone inCone inCone_freeClosed inCone_semantics)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (ActionLaws)
open ConstructionProbeTarget (TargetLaws)
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The order-only part of the source's existing height function. -/
def HeightOrder (D mul R H : M.Carrier .set) : Prop := MapsTo D R H ∧
  (∀ x c, PureKuratowski.PairMember M x c H → ∃ p, (Project.FirstOrderSemantics.reduct M).mem p c) ∧
  (∀ x y c d, PureKuratowski.PairMember M x c H → PureKuratowski.PairMember M y d H →
    Divides D mul x y → Subset c d)

def HeightFamily (D S A H s family : M.Carrier .set) : Prop := ∀ c,
  (Project.FirstOrderSemantics.reduct M).mem c family ↔ ∃ x,
    (Project.FirstOrderSemantics.reduct M).mem x D ∧ InCone S A x s ∧ PureKuratowski.PairMember M x c H

def Floor (D S A H s v : M.Carrier .set) : Prop := ∃ family,
  HeightFamily D S A H s family ∧ UpperBound family v ∧ ∀ t, UpperBound family t → Subset v t

def Graph (D S A H F : M.Carrier .set) : Prop := ∀ s v,
  PureKuratowski.PairMember M s v F ↔ (Project.FirstOrderSemantics.reduct M).mem s S ∧ Floor D S A H s v

def FloorLaws (D S A K H F : M.Carrier .set) : Prop := ∀ s v,
  PureKuratowski.PairMember M s v F →
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p v) ∧
    (∀ x c, (Project.FirstOrderSemantics.reduct M).mem x D → InCone S A x s →
      PureKuratowski.PairMember M x c H → Subset c v) ∧
    (∀ t c, PureKuratowski.PairMember M s t K → PureKuratowski.PairMember M t c H → Subset v c)

def heightValue {m : Nat} (D S A H s c : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound D.succ))
    (.conj (inCone S.succ A.succ 0 s.succ)
      (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ 0 c.succ))))

theorem heightValue_freeClosed {m : Nat} (D S A H s c : Fin m) : (heightValue D S A H s c).FreeClosed := by
  simp -implicitDefEqProofs [heightValue,Definitional.Formula.FreeClosed,inCone_freeClosed,ProjectSyntax.freeClosed]

theorem heightValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D S A H s c : Fin m) :
    Project.Formula.satisfies env (heightValue D S A H s c) ↔ ∃ x,
      (Project.FirstOrderSemantics.reduct M).mem x (env.bound D) ∧ InCone (env.bound S) (env.bound A) x (env.bound s) ∧
      PureKuratowski.PairMember M x (env.bound c) (env.bound H) := by
  simp only [heightValue,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,inCone_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def heightFamily {m : Nat} (D S A H s family : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound family.succ)) (heightValue D.succ S.succ A.succ H.succ s.succ 0))

theorem heightFamily_freeClosed {m : Nat} (D S A H s family : Fin m) : (heightFamily D S A H s family).FreeClosed := by
  simp -implicitDefEqProofs [heightFamily,Definitional.Formula.FreeClosed,heightValue_freeClosed]

theorem heightFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D S A H s family : Fin m) :
    Project.Formula.satisfies env (heightFamily D S A H s family) ↔
      HeightFamily (env.bound D) (env.bound S) (env.bound A) (env.bound H) (env.bound s) (env.bound family) := by
  simp only [heightFamily,HeightFamily,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,heightValue_semantics hM]
  rfl

def floor {m : Nat} (D S A H s v : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (heightFamily D.succ S.succ A.succ H.succ s.succ 0) (supremum 0 v.succ))

theorem floor_freeClosed {m : Nat} (D S A H s v : Fin m) : (floor D S A H s v).FreeClosed := by
  simp -implicitDefEqProofs [floor,Definitional.Formula.FreeClosed,heightFamily_freeClosed,supremum_freeClosed]

theorem floor_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D S A H s v : Fin m) :
    Project.Formula.satisfies env (floor D S A H s v) ↔
      Floor (env.bound D) (env.bound S) (env.bound A) (env.bound H) (env.bound s) (env.bound v) := by
  simp only [floor,Floor,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    heightFamily_semantics hM,supremum_semantics]
  rfl

theorem exists_height_family (hM : FirstOrder.Theory.Models M nativeZF) {D S A H s R : M.Carrier .set}
    (hH : MapsTo D R H) : ∃ family, HeightFamily D S A H s family ∧ Subset family R := by
  let schema : Project.UnarySchema 5 := {
    body := heightValue 1 2 3 4 5 0
    freeClosed := heightValue_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases D (Fin.cases S (Fin.cases A (Fin.cases H (fun _ => s)))), free := fun _ => D }
  obtain ⟨family,hf⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env R
  have he (c : M.Carrier .set) : Project.Formula.satisfies (env.push c) schema.body ↔
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x D ∧ InCone S A x s ∧ PureKuratowski.PairMember M x c H :=
    heightValue_semantics hM (env.push c) 1 2 3 4 5 0
  refine ⟨family,fun c => ⟨fun h => (he c).mp ((hf c).mp h).2,?_⟩,fun c h => ((hf c).mp h).1⟩
  intro hc
  obtain ⟨x,hx,hcone,hxc⟩ := hc
  exact (hf c).mpr ⟨hH.2 x c hxc,(he c).mpr ⟨x,hx,hcone,hxc⟩⟩

theorem floor_unique (hM : FirstOrder.Theory.Models M nativeZF) {D S A H s v u : M.Carrier .set}
    (hv : Floor D S A H s v) (hu : Floor D S A H s u) : v = u := by
  obtain ⟨f,hf,hfv,hv⟩ := hv
  obtain ⟨g,hg,hgu,hu⟩ := hu
  have he : f = g := (ModelTransfer.extensionality hM).eq_of_same_members f g (fun c => (hf c).trans (hg c).symm)
  subst g
  exact (ModelTransfer.extensionality hM).eq_of_same_members v u (fun p => ⟨hv u hgu p,hu v hfv p⟩)

section Bounds
variable {hM : FirstOrder.Theory.Models M nativeZF}
variable {w Q R D mul e S I A K projection T H : M.Carrier .set}
variable (hm : LeftCancelMonoid D mul e) (hI : Representatives D S I) (hA : MapsTo I S A)
variable (hK : MapsTo S D K) (hTarget : TargetLaws mul projection T A K) (hH : HeightOrder D mul R H)
include hm hI hA hK hTarget hH

theorem family_bound {s t c family : M.Carrier .set} (ht : PureKuratowski.PairMember M s t K)
    (hc : PureKuratowski.PairMember M t c H) (hf : HeightFamily D S A H s family) : UpperBound family c := by
  intro v hv
  obtain ⟨x,_,hx,hxv⟩ := (hf v).mp hv
  exact hH.2.2 x t v c hxv hc (ConstructionProbeAlphabet.dvd_target_of_inCone hm hI hA hK hTarget hx ht)

theorem exists_floor (hR : CutCarrier hM w Q R) {s : M.Carrier .set}
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) :
    ∃ v, Cut hM w Q v ∧ Floor D S A H s v := by
  obtain ⟨family,hf,hfR⟩ := exists_height_family hM (S := S) (A := A) (s := s) hH.1
  obtain ⟨t,ht,_⟩ := hK.1.2 s hs
  obtain ⟨c,hc,_⟩ := hH.1.1.2 t (hK.2 s t ht)
  obtain ⟨v,hv,hu,hl⟩ := bounded_union hM hR hfR ((hR c).mp (hH.1.2 t c hc))
    (family_bound hm hI hA hK hTarget hH ht hc hf)
  exact ⟨v,hv,family,hf,hu,hl⟩

theorem floor_bounds (hAction : ActionLaws mul e S A) {s v : M.Carrier .set}
    (hs : (Project.FirstOrderSemantics.reduct M).mem s S) (hv : Floor D S A H s v) :
    (∃ p, (Project.FirstOrderSemantics.reduct M).mem p v) ∧
    (∀ x c, (Project.FirstOrderSemantics.reduct M).mem x D → InCone S A x s →
      PureKuratowski.PairMember M x c H → Subset c v) ∧
    (∀ t c, PureKuratowski.PairMember M s t K → PureKuratowski.PairMember M t c H → Subset v c) := by
  obtain ⟨family,hf,hu,hl⟩ := hv
  obtain ⟨c,hc,_⟩ := hH.1.1.2 e hm.1.1
  obtain ⟨p,hp⟩ := hH.2.1 e c hc
  refine ⟨⟨p,hu c ((hf c).mpr ⟨e,hm.1.1,ConstructionProbeCones.one_inCone hAction hs,hc⟩) p hp⟩,?_,?_⟩
  · exact fun x c hx hcone hxc => hu c ((hf c).mpr ⟨x,hx,hcone,hxc⟩)
  · exact fun t c ht hc => hl c (family_bound hm hI hA hK hTarget hH ht hc hf)

theorem exists_floor_graph (hR : CutCarrier hM w Q R) (hAction : ActionLaws mul e S A) :
    ∃ F, MapsTo S R F ∧ Graph D S A H F ∧ FloorLaws D S A K H F := by
  let schema : Project.BinarySchema 4 := {
    body := floor 2 3 4 5 1 0
    freeClosed := floor_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases D (Fin.cases S (Fin.cases A (fun _ => H))), free := fun _ => D }
  have he (s v : M.Carrier .set) : schema.denote env s v ↔ Floor D S A H s v :=
    floor_semantics hM ((env.push s).push v) 2 3 4 5 1 0
  obtain ⟨F,hF,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := S) (target := R) (by
      intro s hs
      obtain ⟨v,_,hv⟩ := exists_floor hm hI hA hK hTarget hH hR hs
      exact ⟨v,(he s v).mpr hv⟩) (by
      intro s _ v u hv hu
      exact floor_unique hM ((he s v).mp hv) ((he s u).mp hu)) (by
      intro s v hs hv
      obtain ⟨u,hu,hfu⟩ := exists_floor hm hI hA hK hTarget hH hR hs
      exact (floor_unique hM hfu ((he s v).mp hv)) ▸ ((hR u).mpr hu))
  have hg : Graph D S A H F := fun s v => (hgraph s v).trans (and_congr_right (fun _ => he s v))
  refine ⟨F,(ForcingSupportSize.native_mapsTo hM S R F).mpr hF,hg,?_⟩
  intro s v hv
  obtain ⟨hs,hv⟩ := (hg s v).mp hv
  exact floor_bounds hm hI hA hK hTarget hH hAction hs hv

end Bounds
end PPAC.Migration.ConstructionProbeLetterFloor
