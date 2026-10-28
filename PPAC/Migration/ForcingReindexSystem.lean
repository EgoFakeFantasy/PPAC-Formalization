/- Pinned QuotientTransport.ReindexIso.available_iff/availability/fiberEquiv:199-249.
Source and target are DISTINCT actual systems. Reuse permute_sub, fixed-sub
availability, native restrictions and actual function-family uniqueness. -/
import PPAC.Migration.ForcingSystemFibers

namespace PPAC.Migration.ForcingReindexSystem
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (CompositionGraph Permutation)
open ForcingSystemAvailability (Available Carrier)
open ForcingSystemFibers (Fiber)
open ForcingEligibleRestriction (Restricts)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Apps (D pi objects targets apps : M.Carrier .set) : Prop :=
  ∀ r R Or OR, CompositionGraph D pi r R → PureKuratowski.PairMember M r Or objects →
    PureKuratowski.PairMember M R OR targets → ∃ f, PureKuratowski.PairMember M r f apps ∧
      Injection Or OR f ∧ ∀ y, (Project.FirstOrderSemantics.reduct M).mem y OR →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x Or ∧ PureKuratowski.PairMember M x y f

def Natural (D pi maps targetMaps apps : M.Carrier .set) : Prop :=
  ∀ r s R S z Z f g a b x y X Y, CompositionGraph D pi r R → CompositionGraph D pi s S →
    PureKuratowski.Code M z s r → PureKuratowski.Code M Z S R →
    PureKuratowski.PairMember M z f maps → PureKuratowski.PairMember M Z g targetMaps →
    PureKuratowski.PairMember M r a apps → PureKuratowski.PairMember M s b apps →
    PureKuratowski.PairMember M x y f → PureKuratowski.PairMember M x X b →
    PureKuratowski.PairMember M y Y a → PureKuratowski.PairMember M X Y g

theorem app_data {D pi objects targets diagrams image apps r R Or OR f : M.Carrier .set}
    (hMap : MapsTo diagrams image apps) (hApps : Apps D pi objects targets apps)
    (hR : CompositionGraph D pi r R) (hr : PureKuratowski.PairMember M r Or objects)
    (hT : PureKuratowski.PairMember M R OR targets) (hf : PureKuratowski.PairMember M r f apps) :
    Injection Or OR f ∧ ∀ y, (Project.FirstOrderSemantics.reduct M).mem y OR →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x Or ∧ PureKuratowski.PairMember M x y f := by
  obtain ⟨g,hg,hInj,hOnto⟩ := hApps r R Or OR hR hr hT
  have he := ForcingConditionGraphs.function_unique hMap.1 hf hg
  exact he.symm ▸ ⟨hInj,hOnto⟩

theorem available_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi
      r R Or OR a x y n : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hp : Permutation I pi)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects) (hTargets : MapsTo diagrams targetImage targets)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hTargetMaps : MapsTo S targetMapImage targetMaps)
    (hSys : ForcingEligibleSystem.System D objects maps) (hTSys : ForcingEligibleSystem.System D targets targetMaps)
    (hAppMap : MapsTo diagrams appImage apps) (hApps : Apps D pi objects targets apps)
    (hNatural : Natural D pi maps targetMaps apps)
    (hR : CompositionGraph D pi r R) (hr : PureKuratowski.PairMember M r Or objects)
    (hT : PureKuratowski.PairMember M R OR targets) (ha : PureKuratowski.PairMember M r a apps)
    (hxy : PureKuratowski.PairMember M x y a) (hn : (Project.FirstOrderSemantics.reduct M).mem n D) :
    Available D mul targets targetMaps R y n ↔ Available D mul objects maps r x n := by
  have hrI := (hDiagrams r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  obtain ⟨s,hsI,hSub⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 n hn) hrI
  obtain ⟨t,htI,ht⟩ := ForcingDiagramAction.exists_permute hM hp hsI
  have hTSub := ForcingDiagramOrder.permute_sub hR ht hSub
  obtain ⟨Os,hs,_⟩ := hObj.1.2 s ((hDiagrams s).mpr hsI)
  obtain ⟨OS,hst,_⟩ := hTargets.1.2 t ((hDiagrams t).mpr htI)
  obtain ⟨z,f,hz,hf,hfMap⟩ := ForcingSystemAvailability.exists_map hM hObj hS hMaps hSys hr hs ⟨n,hn,hSub⟩
  obtain ⟨Z,g,hZ,hg,hgMap⟩ := ForcingSystemAvailability.exists_map hM hTargets hS hTargetMaps hTSys hT hst ⟨n,hn,hTSub⟩
  obtain ⟨b,hb,hbInj,hbOnto⟩ := hApps s t Os OS ht hs hst
  have haData := app_data hAppMap hApps hR hr hT ha
  rw [ForcingSystemFibers.available_iff_at_sub hM hDiagrams hTargets hTargetMaps hst hTSub hZ hg,
    ForcingSystemFibers.available_iff_at_sub hM hDiagrams hObj hMaps hs hSub hz hf]
  constructor
  · rintro ⟨v,hv,hvy⟩
    obtain ⟨u,hu,huv⟩ := hbOnto v hv
    obtain ⟨c,huc,_⟩ := hfMap.1.2 u hu
    obtain ⟨d,hcd,_⟩ := haData.1.1.1.2 c (hfMap.2 u c huc)
    have hvd := hNatural r s R t z Z f g a b u c v d hR ht hz hZ hf hg ha hb huc huv hcd
    have he := ForcingConditionGraphs.function_unique hgMap.1 hvd hvy
    have hc := haData.1.2 c x y (he ▸ hcd) hxy
    exact ⟨u,hu,hc ▸ huc⟩
  · rintro ⟨u,hu,hux⟩
    obtain ⟨v,huv,_⟩ := hbInj.1.1.2 u hu
    exact ⟨v,hbInj.1.2 u v huv,hNatural r s R t z Z f g a b u x v y hR ht hz hZ hf hg ha hb hux huv hxy⟩

def PreservesAvailability (D mul pi objects maps targets targetMaps apps : M.Carrier .set) : Prop :=
  ∀ r R Or OR a x y n, CompositionGraph D pi r R → PureKuratowski.PairMember M r Or objects →
    PureKuratowski.PairMember M R OR targets → PureKuratowski.PairMember M r a apps →
    PureKuratowski.PairMember M x y a → (Project.FirstOrderSemantics.reduct M).mem n D →
    (Available D mul targets targetMaps R y n ↔ Available D mul objects maps r x n)

theorem carrier_iff {D mul pi objects maps targets targetMaps apps r R Or OR a x y i U : M.Carrier .set}
    (hPres : PreservesAvailability D mul pi objects maps targets targetMaps apps)
    (hR : CompositionGraph D pi r R) (hr : PureKuratowski.PairMember M r Or objects)
    (hT : PureKuratowski.PairMember M R OR targets) (ha : PureKuratowski.PairMember M r a apps)
    (hxy : PureKuratowski.PairMember M x y a) :
    Carrier D mul objects maps r x i U ↔ Carrier D mul targets targetMaps R y i U := by
  constructor
  · intro h n
    constructor
    · intro hn
      obtain ⟨hnD,hni,hnA⟩ := (h n).mp hn
      exact ⟨hnD,hni,(hPres r R Or OR a x y n hR hr hT ha hxy hnD).mpr hnA⟩
    · rintro ⟨hnD,hni,hnA⟩
      exact (h n).mpr ⟨hnD,hni,(hPres r R Or OR a x y n hR hr hT ha hxy hnD).mp hnA⟩
  · intro h n
    constructor
    · intro hn
      obtain ⟨hnD,hni,hnA⟩ := (h n).mp hn
      exact ⟨hnD,hni,(hPres r R Or OR a x y n hR hr hT ha hxy hnD).mp hnA⟩
    · rintro ⟨hnD,hni,hnA⟩
      exact (h n).mpr ⟨hnD,hni,(hPres r R Or OR a x y n hR hr hT ha hxy hnD).mpr hnA⟩

theorem fiber_bijection (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul pi objects maps targets targetMaps diagrams appImage apps r R Or OR a i U X Y : M.Carrier .set}
    (hAppMap : MapsTo diagrams appImage apps) (hApps : Apps D pi objects targets apps)
    (hPres : PreservesAvailability D mul pi objects maps targets targetMaps apps)
    (hR : CompositionGraph D pi r R) (hr : PureKuratowski.PairMember M r Or objects)
    (hT : PureKuratowski.PairMember M R OR targets) (ha : PureKuratowski.PairMember M r a apps)
    (hX : Fiber D mul objects maps r Or i U X) (hY : Fiber D mul targets targetMaps R OR i U Y) :
    ∃ b, Injection X Y b ∧ Restricts b a X ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y Y →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x y b := by
  have hData := app_data hAppMap hApps hR hr hT ha
  have hImage : ∀ x y, PureKuratowski.PairMember M x y a →
      ((Project.FirstOrderSemantics.reduct M).mem x X ↔ (Project.FirstOrderSemantics.reduct M).mem y Y) := by
    intro x y hxy
    exact (hX x).trans ((and_congr (iff_of_true (ForcingConditionGraphs.function_input hData.1.1.1 hxy)
      (hData.1.1.2 x y hxy)) (carrier_iff hPres hR hr hT ha hxy)).trans (hY y).symm)
  obtain ⟨b,hb⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) a X
  have hEdge : Restricts b a X := fun x y => (hb.2 x y).trans and_comm
  have hMap : MapsTo X Y b := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro row hrow
      obtain ⟨x,y,hcode⟩ := hb.1 row hrow
      exact ⟨x,y,((hb.2 x y).mp ⟨row,hcode,hrow⟩).1,hcode⟩
    · intro x hx
      obtain ⟨y,hxy,_⟩ := hData.1.1.1.2 x ((hX x).mp hx).1
      exact ⟨y,(hEdge x y).mpr ⟨hxy,hx⟩,fun z hxz =>
        ForcingConditionGraphs.function_unique hData.1.1.1 ((hEdge x z).mp hxz).1 hxy⟩
    · intro x y hxy
      obtain ⟨hxy,hx⟩ := (hEdge x y).mp hxy
      exact (hImage x y hxy).mp hx
  refine ⟨b,ForcingEligibleRestriction.restrict_injective hData.1 hEdge hMap,hEdge,?_⟩
  intro y hy
  obtain ⟨x,_,hxy⟩ := hData.2 y ((hY y).mp hy).1
  have hx := (hImage x y hxy).mpr hy
  exact ⟨x,hx,(hEdge x y).mpr ⟨hxy,hx⟩⟩

def AllFibers (D mul pi objects maps targets targetMaps apps : M.Carrier .set) : Prop :=
  ∀ r R Or OR a i U X Y, CompositionGraph D pi r R → PureKuratowski.PairMember M r Or objects →
    PureKuratowski.PairMember M R OR targets → PureKuratowski.PairMember M r a apps →
    Fiber D mul objects maps r Or i U X → Fiber D mul targets targetMaps R OR i U Y →
    ∃ b, Injection X Y b ∧ Restricts b a X ∧
      ∀ y, (Project.FirstOrderSemantics.reduct M).mem y Y →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x y b


def appsF {m : Nat} (D pi objects targets apps : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ pi.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge targets.succ.succ.succ.succ 2 0)) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge apps.succ.succ.succ.succ.succ 4 0)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 2 1)) (.forallE (.imp (.mem (.bound 0) (.bound 2)) (.existsE (.conj (.mem (.bound 0) (.bound 4)) (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 1))))))))))))))))

theorem appsF_freeClosed {m : Nat} (D pi objects targets apps : Fin m) :
    (appsF D pi objects targets apps).FreeClosed := by
  simp -implicitDefEqProofs [appsF,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem appsF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D pi objects targets apps : Fin m) :
    Project.Formula.satisfies env (appsF D pi objects targets apps) ↔ Apps (env.bound D) (env.bound pi) (env.bound objects) (env.bound targets) (env.bound apps) := by
  simp only [appsF,Apps,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.compositionGraph_semantics (M := M),KuratowskiZF.source_edge,ForcingSupportSize.injection_semantics (M := M)]
  rfl

def natural {m : Nat} (D pi maps targetMaps apps : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 11)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 10)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered 9 12 13)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered 8 10 11)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 7)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge apps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 5)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge apps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 4)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 7 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 4 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 5 2 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge 6 1 0)))))))))))))))))))))))))))

theorem natural_freeClosed {m : Nat} (D pi maps targetMaps apps : Fin m) :
    (natural D pi maps targetMaps apps).FreeClosed := by
  simp -implicitDefEqProofs [natural,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem natural_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D pi maps targetMaps apps : Fin m) :
    Project.Formula.satisfies env (natural D pi maps targetMaps apps) ↔ Natural (env.bound D) (env.bound pi) (env.bound maps) (env.bound targetMaps) (env.bound apps) := by
  simp only [natural,Natural,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.compositionGraph_semantics (M := M),KuratowskiZF.source_edge,KuratowskiZF.source_code]
  rfl

def preservesAvailability {m : Nat} (D mul pi objects maps targets targetMaps apps : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ 7 6)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ.succ.succ.succ.succ 7 5)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge targets.succ.succ.succ.succ.succ.succ.succ.succ 6 4)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge apps.succ.succ.succ.succ.succ.succ.succ.succ 7 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 3 2 1)) (.imp (.mem (.bound 0) (.bound D.succ.succ.succ.succ.succ.succ.succ.succ)) (.iff (ProjectSyntax.encode id (ForcingSystemAvailability.available D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ 6 1 0)) (ProjectSyntax.encode id (ForcingSystemAvailability.available D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ 7 2 0)))))))))))))))))

theorem preservesAvailability_freeClosed {m : Nat} (D mul pi objects maps targets targetMaps apps : Fin m) :
    (preservesAvailability D mul pi objects maps targets targetMaps apps).FreeClosed := by
  simp -implicitDefEqProofs [preservesAvailability,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem preservesAvailability_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul pi objects maps targets targetMaps apps : Fin m) :
    Project.Formula.satisfies env (preservesAvailability D mul pi objects maps targets targetMaps apps) ↔ PreservesAvailability (env.bound D) (env.bound mul) (env.bound pi) (env.bound objects) (env.bound maps) (env.bound targets) (env.bound targetMaps) (env.bound apps) := by
  simp only [preservesAvailability,PreservesAvailability,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.compositionGraph_semantics (M := M),KuratowskiZF.source_edge,Project.Formula.satisfies_iff_iff,ForcingSystemAvailability.available_semantics (M := M)]
  rfl

def allFibers {m : Nat} (D mul pi objects maps targets targetMaps apps : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 7)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge targets.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 5)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge apps.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 4)) (.imp (ProjectSyntax.encode id (ForcingSystemFibers.fiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6 3 2 1)) (.imp (ProjectSyntax.encode id (ForcingSystemFibers.fiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ targets.succ.succ.succ.succ.succ.succ.succ.succ.succ targetMaps.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 5 3 2 0)) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 2 1)) (.conj (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw 0 5 2)) (.forallE (.imp (.mem (.bound 0) (.bound 2)) (.existsE (.conj (.mem (.bound 0) (.bound 4)) (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 1))))))))))))))))))))))))

theorem allFibers_freeClosed {m : Nat} (D mul pi objects maps targets targetMaps apps : Fin m) :
    (allFibers D mul pi objects maps targets targetMaps apps).FreeClosed := by
  simp -implicitDefEqProofs [allFibers,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem allFibers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul pi objects maps targets targetMaps apps : Fin m) :
    Project.Formula.satisfies env (allFibers D mul pi objects maps targets targetMaps apps) ↔ AllFibers (env.bound D) (env.bound mul) (env.bound pi) (env.bound objects) (env.bound maps) (env.bound targets) (env.bound targetMaps) (env.bound apps) := by
  simp only [allFibers,AllFibers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.compositionGraph_semantics (M := M),KuratowskiZF.source_edge,ForcingSystemFibers.fiber_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingEligibleRestriction.edgeLaw_semantics (M := M)]
  rfl

def transportSentence {k : Nat} (D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targets diagrams targetImage)) (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo targetMaps S targetMapImage)) (.imp (ForcingEligibleSystem.system D objects maps) (.imp (ForcingEligibleSystem.system D targets targetMaps) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo apps diagrams appImage)) (.imp (appsF D pi objects targets apps) (.imp (natural D pi maps targetMaps apps) (.conj (preservesAvailability D mul pi objects maps targets targetMaps apps) (allFibers D mul pi objects maps targets targetMaps apps)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingEligibleSystem.system_freeClosed,appsF_freeClosed,natural_freeClosed,preservesAvailability_freeClosed,allFibers_freeClosed]

theorem transport_models {k : Nat} (D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (transportSentence D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (transportSentence D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingEligibleSystem.system_semantics hM,appsF_semantics hM,natural_semantics hM,preservesAvailability_semantics hM,allFibers_semantics hM]
  intro hm hp hDiagrams hObj hTargets hS hMaps hTargetMaps hSys hTSys hAppMap hApps hNatural
  have hPres : PreservesAvailability (bound D) (bound mul) (bound pi) (bound objects) (bound maps) (bound targets) (bound targetMaps) (bound apps) :=
    fun _ _ _ _ _ _ _ _ hR hr hT ha hxy hn => available_iff hM hm hp hDiagrams hObj hTargets hS hMaps hTargetMaps hSys hTSys hAppMap hApps hNatural hR hr hT ha hxy hn
  exact ⟨hPres,fun _ _ _ _ _ _ _ _ _ hR hr hT ha hX hY => fiber_bijection hM hAppMap hApps hPres hR hr hT ha hX hY⟩

theorem transport_kernel_certificate {k : Nat} (D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (transportSentence D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi)) :=
  ModelTransfer.derives (fun _ hM => transport_models D I mul e diagrams objImage objects S mapImage maps targetImage targets targetMapImage targetMaps appImage apps pi hM)

end PPAC.Migration.ForcingReindexSystem
