/- Pinned QuotientActions.labelTransport:291-302.
The app at a diagram is the actual label permutation restricted to its range.
Construct its entire internal function family and consume ReindexIso transport. -/
import PPAC.Migration.ForcingReindexSystem
import PPAC.Migration.ForcingLabelSystem

namespace PPAC.Migration.ForcingLabelTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (CompositionGraph Permutation)
open ForcingEligibleRestriction (Restricts)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Row (I objects pi r f : M.Carrier .set) : Prop := ∃ Or,
  PureKuratowski.PairMember M r Or objects ∧ MapsTo Or I f ∧ Restricts f pi Or

def Family (I diagrams objects pi apps : M.Carrier .set) : Prop := ∀ r f,
  PureKuratowski.PairMember M r f apps ↔ (Project.FirstOrderSemantics.reduct M).mem r diagrams ∧ Row I objects pi r f

theorem exists_row (hM : FirstOrder.Theory.Models M nativeZF)
    {D I diagrams objImage objects pi r : M.Carrier .set}
    (hp : Permutation I pi) (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects) (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r diagrams) : ∃ f, Row I objects pi r f := by
  obtain ⟨Or,hOr,_⟩ := hObj.1.2 r hr
  have hrI := (hDiagrams r).mp hr
  have hRange := ((hObjects r Or).mp hOr).2
  have hSub : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x Or → (Project.FirstOrderSemantics.reduct M).mem x I := by
    intro x hx
    obtain ⟨k,_,hkx⟩ := (hRange x).mp hx
    exact hrI.1.2 k x hkx
  obtain ⟨f,hf⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) pi Or
  have hEdge : Restricts f pi Or := fun x y => (hf.2 x y).trans and_comm
  refine ⟨f,Or,hOr,⟨⟨?_,?_⟩,?_⟩,hEdge⟩
  · intro row hrow
    obtain ⟨x,y,hcode⟩ := hf.1 row hrow
    exact ⟨x,y,((hf.2 x y).mp ⟨row,hcode,hrow⟩).1,hcode⟩
  · intro x hx
    obtain ⟨y,hxy,_⟩ := hp.1.1.2 x (hSub x hx)
    exact ⟨y,(hEdge x y).mpr ⟨hxy,hx⟩,fun z hxz =>
      ForcingConditionGraphs.function_unique hp.1.1 ((hEdge x z).mp hxz).1 hxy⟩
  · intro x y hxy
    exact hp.1.2 x y ((hEdge x y).mp hxy).1

theorem row_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {I diagrams objImage objects pi r f g : M.Carrier .set}
    (hObj : MapsTo diagrams objImage objects) (hf : Row I objects pi r f) (hg : Row I objects pi r g) : f = g := by
  obtain ⟨Or,hr,hf,hR⟩ := hf
  obtain ⟨Os,hs,hg,hS⟩ := hg
  have he := ForcingConditionGraphs.function_unique hObj.1 hr hs
  subst Os
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM Or I f).mp hf).1.1
    ((ForcingSupportSize.native_mapsTo hM Or I g).mp hg).1.1
    (fun x y => (hR x y).trans (hS x y).symm)

theorem row_bijective {D I diagrams objImage objects pi r R Or OR f : M.Carrier .set}
    (hp : Permutation I pi) (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects) (hR : CompositionGraph D pi r R)
    (hr : PureKuratowski.PairMember M r Or objects) (hT : PureKuratowski.PairMember M R OR objects)
    (hf : Row I objects pi r f) : Injection Or OR f ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y OR →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x Or ∧ PureKuratowski.PairMember M x y f := by
  obtain ⟨Or',hr',hMap,hRestricts⟩ := hf
  have he := ForcingConditionGraphs.function_unique hObj.1 hr hr'
  subst Or'
  have hSource := ((hObjects r Or).mp hr).2
  have hTarget := ((hObjects R OR).mp hT).2
  refine ⟨⟨⟨hMap.1,?_⟩,?_⟩,?_⟩
  · intro x y hxy
    obtain ⟨hpxy,hx⟩ := (hRestricts x y).mp hxy
    obtain ⟨k,hk,hkx⟩ := (hSource x).mp hx
    exact (hTarget y).mpr ⟨k,hk,(hR k y).mpr ⟨hk,x,hkx,hpxy⟩⟩
  · intro x y z hx hy
    exact hp.2.1 x y z ((hRestricts x z).mp hx).1 ((hRestricts y z).mp hy).1
  · intro y hy
    obtain ⟨k,hk,hky⟩ := (hTarget y).mp hy
    obtain ⟨_,x,hkx,hxy⟩ := (hR k y).mp hky
    have hx := (hSource x).mpr ⟨k,hk,hkx⟩
    exact ⟨x,hx,(hRestricts x y).mpr ⟨hxy,hx⟩⟩

theorem apps_of_family {D I diagrams objImage objects pi appImage apps : M.Carrier .set}
    (hp : Permutation I pi) (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hAppMap : MapsTo diagrams appImage apps) (hFamily : Family I diagrams objects pi apps) :
    ForcingReindexSystem.Apps D pi objects objects apps := by
  intro r R Or OR hR hr hT
  obtain ⟨f,hf,_⟩ := hAppMap.1.2 r (ForcingConditionGraphs.function_input hObj.1 hr)
  exact ⟨f,hf,row_bijective hp hObj hObjects hR hr hT ((hFamily r f).mp hf).2⟩

theorem natural_of_family {D I diagrams objImage objects pi S maps apps : M.Carrier .set}
    (hp : Permutation I pi) (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hMaps : ForcingLabelSystem.Maps objects S maps) (hFamily : Family I diagrams objects pi apps) :
    ForcingReindexSystem.Natural D pi maps maps apps := by
  intro r s R T z Z f g a b x y X Y hR hT hz hZ hf hg ha hb hxy hxX hyY
  obtain ⟨s',r',Os,Or,hz',hs,hr,_,hId⟩ := ((hMaps z f).mp hf).2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  obtain ⟨T',R',OT,OR,hZ',hOT,_,_,hG⟩ := ((hMaps Z g).mp hg).2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hZ hZ'
  have hbRow := ((hFamily s b).mp hb).2
  have hbData := row_bijective hp hObj hObjects hT hs hOT hbRow
  obtain ⟨_,_,_,hbRestricts⟩ := hbRow
  obtain ⟨_,_,_,haRestricts⟩ := ((hFamily r a).mp ha).2
  have he := ((hId x y).mp hxy).2
  subst y
  have hXY := ForcingConditionGraphs.function_unique hp.1.1 ((hbRestricts x X).mp hxX).1 ((haRestricts x Y).mp hyY).1
  exact (hG X Y).mpr ⟨hbData.1.1.2 x X hxX,hXY⟩


def row {m : Nat} (I objects pi r f : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ r.succ 0))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f.succ 0 I.succ))
      (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw f.succ pi.succ 0))))

theorem row_freeClosed {m : Nat} (I objects pi r f : Fin m) : (row I objects pi r f).FreeClosed := by
  simp -implicitDefEqProofs [row,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem row_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I objects pi r f : Fin m) :
    Project.Formula.satisfies env (row I objects pi r f) ↔ Row (env.bound I) (env.bound objects) (env.bound pi) (env.bound r) (env.bound f) := by
  simp only [row,Row,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingEligibleRestriction.edgeLaw_semantics (M := M)]
  rfl

def family {m : Nat} (I diagrams objects pi apps : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge apps.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound diagrams.succ.succ)) (row I.succ.succ objects.succ.succ pi.succ.succ 1 0))))

theorem family_freeClosed {m : Nat} (I diagrams objects pi apps : Fin m) : (family I diagrams objects pi apps).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,row_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I diagrams objects pi apps : Fin m) :
    Project.Formula.satisfies env (family I diagrams objects pi apps) ↔ Family (env.bound I) (env.bound diagrams) (env.bound objects) (env.bound pi) (env.bound apps) := by
  simp only [family,Family,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,row_semantics hM]
  rfl

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    {D I diagrams objImage objects pi : M.Carrier .set}
    (hp : Permutation I pi) (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects) (hObjects : ForcingLabelSystem.Objects D diagrams objects) :
    ∃ image apps, MapsTo diagrams image apps ∧ Family I diagrams objects pi apps := by
  let schema : Project.BinarySchema 3 := { body := row 2 3 4 1 0, freeClosed := row_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases I (Fin.cases objects (fun _ => pi)), free := fun _ => diagrams }
  have he r f : schema.denote env r f ↔ Row I objects pi r f := row_semantics hM ((env.push r).push f) 2 3 4 1 0
  have ht : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r diagrams → ∃ f, schema.denote env r f := by
    intro r hr
    obtain ⟨f,hf⟩ := exists_row hM hp hDiagrams hObj hObjects hr
    exact ⟨f,(he r f).mpr hf⟩
  have hu : ∀ r f g, schema.denote env r f → schema.denote env r g → f = g :=
    fun r f g hf hg => row_unique hM hObj ((he r f).mp hf) ((he r g).mp hg)
  obtain ⟨image,hImage⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env diagrams ht hu
  obtain ⟨apps,hApp,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun r _ f g hf hg => hu r f g hf hg)
    (fun r f hr hf => (hImage f).mpr ⟨r,hr,hf⟩)
  exact ⟨image,apps,(ForcingSupportSize.native_mapsTo hM diagrams image apps).mpr hApp,
    fun r f => (hEdge r f).trans (and_congr Iff.rfl (he r f))⟩

def constructionSentence {k : Nat} (D I mul e pi : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e))
      (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi))
        (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ 7)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 5 7 6)) (.conj (ForcingLabelSystem.objectFamily D.succ.succ.succ.succ.succ.succ.succ.succ 7 5) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ 7 4)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2 4 3)) (.conj (ForcingLabelSystem.mapFamily 5 4 2) (.conj (ForcingEligibleSystem.system D.succ.succ.succ.succ.succ.succ.succ.succ 5 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 7 1)) (.conj (family I.succ.succ.succ.succ.succ.succ.succ.succ 7 5 pi.succ.succ.succ.succ.succ.succ.succ.succ 0) (.conj (ForcingReindexSystem.appsF D.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ 5 5 0) (.conj (ForcingReindexSystem.natural D.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ 2 2 0) (.conj (ForcingReindexSystem.preservesAvailability D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ 5 2 5 2 0) (ForcingReindexSystem.allFibers D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ 5 2 5 2 0)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,
      ForcingEligibleSystem.system_freeClosed,family_freeClosed,ForcingReindexSystem.appsF_freeClosed,
      ForcingReindexSystem.natural_freeClosed,ForcingReindexSystem.preservesAvailability_freeClosed,ForcingReindexSystem.allFibers_freeClosed]

theorem construction_models {k : Nat} (D I mul e pi : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e pi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence D I mul e pi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,
    ForcingEligibleSystem.system_semantics hM,family_semantics hM,ForcingReindexSystem.appsF_semantics hM,
    ForcingReindexSystem.natural_semantics hM,ForcingReindexSystem.preservesAvailability_semantics hM,ForcingReindexSystem.allFibers_semantics hM]
  intro hm hp
  obtain ⟨diagrams,objImage,objects,S,mapImage,maps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys⟩ :=
    ForcingLabelSystem.exists_system hM (bound D) (bound I) (bound mul)
  obtain ⟨appImage,apps,hAppMap,hAppsFamily⟩ := exists_family hM hp hDiagrams hObj hObjects
  have hApps := apps_of_family hp hObj hObjects hAppMap hAppsFamily
  have hNatural := natural_of_family hp hObj hObjects hFamily hAppsFamily
  have hPres : ForcingReindexSystem.PreservesAvailability (bound D) (bound mul) (bound pi) objects maps objects maps apps :=
    fun _ _ _ _ _ _ _ _ hR hr hT ha hxy hn => ForcingReindexSystem.available_iff hM hm hp hDiagrams hObj hObj hS hMaps hMaps hSys hSys hAppMap hApps hNatural hR hr hT ha hxy hn
  exact ⟨diagrams,objImage,objects,S,mapImage,maps,appImage,apps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys,hAppMap,hAppsFamily,hApps,hNatural,hPres,
    fun _ _ _ _ _ _ _ _ _ hR hr hT ha hX hY => ForcingReindexSystem.fiber_bijection hM hAppMap hApps hPres hR hr hT ha hX hY⟩

theorem construction_kernel_certificate {k : Nat} (D I mul e pi : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul e pi)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e pi hM)

end PPAC.Migration.ForcingLabelTransport
