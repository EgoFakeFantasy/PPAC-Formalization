/- Pinned BlockTowers.Cell.simulation_surjective/simulationEquiv/rangeAttachment.
Reuse actual cell generation, literal simulation endpoint equations and the
native inverse graph. The range identification fixes every old element and
keeps the SAME terminal range; it does not replace an executed cell by an
assumed attachment or assert that the full flattened step family is assembled. -/
import PPAC.Migration.ConstructionCellParameters
import PPAC.Migration.ConstructionCellPreimage
import PPAC.Migration.ConstructionBlockStages

namespace PPAC.Migration.ConstructionCellSimulationEquiv
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout (Hom SquareComm)
open ConstructionProbeSimulation (EndpointLaws)
open ConstructionCellGeneration (Submonoid Generated)
open ConstructionProbeMappedPath (NodeMap)
open ForcingSupportSize (MapsTo Injection)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (function_input function_unique InverseGraph)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The image of the actual simulation is an ordinary internal submonoid. -/
theorem range_submonoid
    {W WN G GN unit unitN H R : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hmN : LeftCancelMonoid WN GN unitN)
    (hH : Hom W WN G GN unit unitN H) (hR : Range W H R) :
    Submonoid WN GN unitN R := by
  refine ⟨?_,(hR unitN).mpr ⟨unit,hm.1.1,hH.2.1⟩,?_⟩
  · intro y hy
    obtain ⟨x,_,hxy⟩ := (hR y).mp hy
    exact hH.1.2 x y hxy
  · intro x y z hx hy hp
    obtain ⟨a,ha,hax⟩ := (hR x).mp hx
    obtain ⟨b,hb,hby⟩ := (hR y).mp hy
    obtain ⟨c,hc,habc⟩ := (hm.2.1 a ha).1 b hb
    obtain ⟨t,hct,_⟩ := hH.1.1.2 c hc
    have he := (hmN.2.1 x (hH.1.2 a x hax)).2.1 y t z
      (hH.1.2 b y hby) (hH.2.2 a b c x y t habc hax hby hct) hp
    exact (hR z).mpr ⟨c,hc,he ▸ hct⟩

/-- Source simulation_surjective: old and new generators lie in its literal
range. Generation of the actual target cell, not a surjectivity premise on
its extension, closes the argument. All elements/indices are internal. -/
theorem simulation_surjective (hM : FirstOrder.Theory.Models M nativeZF)
    {D N I W WN G GN unit unitN O ON P PN f H : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hmN : LeftCancelMonoid WN GN unitN)
    (hO : MapsTo D W O) (hON : MapsTo N WN ON)
    (hP : MapsTo I W P) (hPN : MapsTo I WN PN)
    (hH : Hom W WN G GN unit unitN H)
    (hOnto : Range D f N) (hEnd : EndpointLaws f H O ON P PN)
    (hGen : Generated N I WN GN unitN ON PN) : Range W H WN := by
  obtain ⟨R,hR⟩ := ConstructionBlockStages.range_exists hM hH.1
  have hOld : MapsTo N R ON := by
    refine ⟨hON.1,?_⟩
    intro y z hyz
    obtain ⟨x,hx,hxy⟩ := (hOnto y).mp (function_input hON.1 hyz)
    obtain ⟨q,hq,_⟩ := hO.1.2 x hx
    exact (hR z).mpr ⟨q,hO.2 x q hq,hEnd.1 x y q z hxy hq hyz⟩
  have hNew : MapsTo I R PN := by
    refine ⟨hPN.1,?_⟩
    intro i z hiz
    obtain ⟨q,hiq,_⟩ := hP.1.2 i (function_input hPN.1 hiz)
    exact (hR z).mpr ⟨q,hP.2 i q hiq,hEnd.2 i q z hiq hiz⟩
  exact (hGen R (range_submonoid hm hmN hH hR) hOld hNew) ▸ hR

/-- Use the existing inverseBijectionWithPairs route. Both inverse
homomorphism laws are derived; no isomorphism is added as a premise. -/
theorem inverse_hom (hM : FirstOrder.Theory.Models M nativeZF)
    {W WN G GN unit unitN H : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hmN : LeftCancelMonoid WN GN unitN)
    (hH : Hom W WN G GN unit unitN H) (hInj : Injection W WN H)
    (hOnto : Range W H WN) :
    ∃ inv, Hom WN W GN G unitN unit inv ∧ InverseGraph H inv := by
  obtain ⟨R,inv,hR,hi,he⟩ := ConstructionCellPreimage.range_inverse hM hInj
  have eR : R = WN := (ModelTransfer.extensionality hM).eq_of_same_members R WN (fun y => by
    rw [hR y,hOnto y]
    exact ⟨fun ⟨x,hxy⟩ => ⟨x,function_input hH.1.1 hxy,hxy⟩,fun ⟨x,_,hxy⟩ => ⟨x,hxy⟩⟩)
  subst R
  refine ⟨inv,⟨hi,(he unitN unit).mpr hH.2.1,?_⟩,fun x y => (he y x).symm⟩
  intro x y z a b c hxyz hxa hyb hzc
  have hax := (he x a).mp hxa
  have hby := (he y b).mp hyb
  have hcz := (he z c).mp hzc
  obtain ⟨t,ht,habt⟩ := (hm.2.1 a (hi.2 x a hxa)).1 b (hi.2 y b hyb)
  obtain ⟨v,htv,_⟩ := hH.1.1.2 t ht
  have ev := (hmN.2.1 x (function_input hi.1 hxa)).2.1 y v z
    (function_input hi.1 hyb) (hH.2.2 a b t x y v habt hax hby htv) hxyz
  have et := hInj.2 t c z (ev ▸ htv) hcz
  exact et ▸ habt

/-- The same actual simulation, now with an internally constructed inverse. -/
theorem simulation_equiv (hM : FirstOrder.Theory.Models M nativeZF)
    {D N I W WN G GN unit unitN O ON P PN f H : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hmN : LeftCancelMonoid WN GN unitN)
    (hO : MapsTo D W O) (hON : MapsTo N WN ON)
    (hP : MapsTo I W P) (hPN : MapsTo I WN PN)
    (hH : Hom W WN G GN unit unitN H) (hInj : Injection W WN H)
    (hOnto : Range D f N) (hEnd : EndpointLaws f H O ON P PN)
    (hGen : Generated N I WN GN unitN ON PN) :
    Range W H WN ∧ ∃ inv, Hom WN W GN G unitN unit inv ∧ InverseGraph H inv := by
  have hs := simulation_surjective hM hm hmN hO hON hP hPN hH hOnto hEnd hGen
  exact ⟨hs,inverse_hom hM hm hmN hH hInj hs⟩

/-- Source rangeAttachment's s.symm.trans g.rangeEquiv. Keep its literal
terminal range R, construct the composite, and prove every old element is
fixed. The mapped cell's actual presentation is supplied by its existing
simulation producer, not replaced by this identification statement. -/
theorem range_identification (hM : FirstOrder.Theory.Models M nativeZF)
    {D N W WN V G GN GV unit unitN unitV O ON f H inv g R : M.Carrier .set}
    (hO : MapsTo D W O) (hON : MapsTo N WN ON)
    (hH : Hom W WN G GN unit unitN H)
    (hInv : Hom WN W GN G unitN unit inv) (hInverse : InverseGraph H inv)
    (hg : Hom W V G GV unit unitV g) (hGInj : Injection W V g)
    (hf : Range D f N) (hOld : NodeMap O g f)
    (hEnd : SquareComm O f H ON)
    (hRange : Range W g R) :
    ∃ embedding, Hom WN V GN GV unitN unitV embedding ∧ Injection WN V embedding ∧ NodeMap inv g embedding ∧
      ConstructionAttachmentCoefficients.OldFixed ON embedding ∧ Range WN embedding R := by
  obtain ⟨embedding,hE,hComp⟩ := ConstructionPushoutPasting.exists_hom_comp hM hInv hg
  refine ⟨embedding,hE,⟨hE.1,?_⟩,hComp,?_,?_⟩
  · intro x y z hxz hyz
    obtain ⟨a,hxa,haz⟩ := (hComp x z).mp hxz
    obtain ⟨b,hyb,hbz⟩ := (hComp y z).mp hyz
    have he := hGInj.2 a b z haz hbz
    subst b
    exact function_unique hH.1.1 ((hInverse a x).mpr hxa) ((hInverse a y).mpr hyb)
  · intro y Q hyQ
    obtain ⟨x,hx,hxy⟩ := (hf y).mp (function_input hON.1 hyQ)
    obtain ⟨q,hxq,_⟩ := hO.1.2 x hx
    have hqQ := (hEnd x q y Q hxq hxy).mpr hyQ
    obtain ⟨q',hxq',hq'y⟩ := (hOld x y).mp hxy
    have eqQ := function_unique hO.1 hxq' hxq
    exact (hComp Q y).mpr ⟨q,(hInverse q Q).mp hqQ,eqQ ▸ hq'y⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨x,hx,hxz⟩ := (hRange z).mp hz
      obtain ⟨y,hxy,_⟩ := hH.1.1.2 x hx
      exact ⟨y,hH.1.2 x y hxy,(hComp y z).mpr ⟨x,(hInverse x y).mp hxy,hxz⟩⟩
    · rintro ⟨y,_,hyz⟩
      obtain ⟨x,hyx,hxz⟩ := (hComp y z).mp hyz
      exact (hRange z).mpr ⟨x,hInv.1.2 y x hyx,hxz⟩

/-- The Merger producer stores the same endpoint equations as a commuting
square and a root-composite graph. Consume those exact existing fields. -/
theorem endpoints_of_square
    {O f H ON P PN : M.Carrier .set}
    (hComm : SquareComm O f H ON) (hRoots : NodeMap P H PN)
    {I W : M.Carrier .set} (hP : MapsTo I W P) : EndpointLaws f H O ON P PN := by
  refine ⟨fun x y q Q hxy hxq hyQ => (hComm x q y Q hxq hxy).mpr hyQ,?_⟩
  intro i q Q hiq hiQ
  obtain ⟨q',hiq',hqQ⟩ := (hRoots i Q).mp hiQ
  exact (function_unique hP.1 hiq' hiq) ▸ hqQ

/-- Both actual Probe presentations discharge generation and monoid laws.
The simulation is the existing producer's graph, with its recorded endpoint
and conservation evidence; the extension inverse is constructed here. -/
theorem probe_equiv (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O
      N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hA : ConstructionProbePushout.Presentation hM w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
    (hB : ConstructionProbePushout.Presentation hM w zero N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON)
    (hH : Hom W WN G GN unit unitN H) (hInj : Injection W WN H)
    (hOnto : Range D f N) (hEnd : EndpointLaws f H O ON P PN) :
    Range W H WN ∧ ∃ inv, Hom WN W GN G unitN unit inv ∧ InverseGraph H inv := by
  have hm := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hA.monoid hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication
  have hmN := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hB.monoid hB.alphabet hB.word hB.b_mem hB.old_unit hB.multiplication
  exact simulation_equiv hM hm hmN hA.old_map hB.old_map hA.probes_map hB.probes_map hH hInj hOnto hEnd
    (ConstructionCellGeneration.probe_generated hM hB hw hz hzw)

/-- Both actual Merger presentations discharge the generator contracts.
The source/target monoid laws are retained from the actual weighted tower. -/
theorem merger_equiv (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P C L projection A W T B G unit O roots
      N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hA : ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hB : ConstructionMergerPushout.Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
    (hm : LeftCancelMonoid W G unit) (hmN : LeftCancelMonoid WN GN unitN)
    (hH : Hom W WN G GN unit unitN H) (hInj : Injection W WN H)
    (hOnto : Range D f N) (hComm : SquareComm O f H ON) (hRoots : NodeMap roots H rootsN) :
    Range W H WN ∧ ∃ inv, Hom WN W GN G unitN unit inv ∧ InverseGraph H inv :=
  simulation_equiv hM hm hmN hA.old_hom.1 hB.old_hom.1 hA.roots_map hB.roots_map hH hInj hOnto
    (endpoints_of_square hComm hRoots hA.roots_map) (ConstructionCellGeneration.merger_generated hM hB hw hz hzw)

def equivalence {m : Nat} (W WN G GN unit unitN H : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingSupportedNames.range W H WN))
    (.existsE (.conj (ConstructionProbePushoutSyntax.hom WN.succ W.succ GN.succ G.succ unitN.succ unit.succ 0)
      (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph H.succ 0))))

theorem equivalence_freeClosed {m : Nat} (W WN G GN unit unitN H : Fin m) :
    (equivalence W WN G GN unit unitN H).FreeClosed := by
  simp -implicitDefEqProofs [equivalence,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed]

theorem equivalence_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W WN G GN unit unitN H : Fin m) :
    Project.Formula.satisfies env (equivalence W WN G GN unit unitN H) ↔
      (Range (env.bound W) (env.bound H) (env.bound WN) ∧ ∃ inv,
        Hom (env.bound WN) (env.bound W) (env.bound GN) (env.bound G) (env.bound unitN) (env.bound unit) inv ∧
        InverseGraph (env.bound H) inv) := by
  simp only [equivalence,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportedNames.range_semantics (M := M),ConstructionProbePushoutSyntax.hom_semantics hM,
    ForcingConditionGraphs.inverseGraph_semantics (M := M)]
  rfl

def identification {m : Nat} (WN V GN GV unitN unitV ON inv g R : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ConstructionProbePushoutSyntax.hom WN.succ V.succ GN.succ GV.succ unitN.succ unitV.succ 0)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 WN.succ V.succ))
      (.conj (ConstructionProbeMappedPathSyntax.nodeMap inv.succ g.succ 0)
        (.conj (ConstructionAttachmentCoefficients.oldFixed ON.succ 0)
          (ProjectSyntax.encode id (ForcingSupportedNames.range WN.succ 0 R.succ))))))

theorem identification_freeClosed {m : Nat} (WN V GN GV unitN unitV ON inv g R : Fin m) :
    (identification WN V GN GV unitN unitV ON inv g R).FreeClosed := by
  simp -implicitDefEqProofs [identification,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
    ConstructionAttachmentCoefficients.oldFixed_freeClosed]

theorem identification_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (WN V GN GV unitN unitV ON inv g R : Fin m) :
    Project.Formula.satisfies env (identification WN V GN GV unitN unitV ON inv g R) ↔
      ∃ embedding, Hom (env.bound WN) (env.bound V) (env.bound GN) (env.bound GV) (env.bound unitN) (env.bound unitV) embedding ∧
        Injection (env.bound WN) (env.bound V) embedding ∧ NodeMap (env.bound inv) (env.bound g) embedding ∧
        ConstructionAttachmentCoefficients.OldFixed (env.bound ON) embedding ∧ Range (env.bound WN) embedding (env.bound R) := by
  simp only [identification,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportedNames.range_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM]
  rfl

def simulationSentence {m : Nat} (D N I W WN G GN unit unitN O ON P PN f H : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W G unit))
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid WN GN unitN))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo O D W))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo ON N WN))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo P I W))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo PN I WN))
      (.imp (ConstructionProbePushoutSyntax.hom W WN G GN unit unitN H)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection H W WN))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D f N))
      (.imp (ConstructionProbeSimulation.endpointLaws f H O ON P PN)
      (.imp (ConstructionCellGeneration.generated N I WN GN unitN ON PN)
      (equivalence W WN G GN unit unitN H))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      equivalence_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbeSimulation.endpointLaws_freeClosed,
      ConstructionCellGeneration.generated_freeClosed]

theorem simulation_models {m : Nat} (D N I W WN G GN unit unitN O ON P PN f H : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (simulationSentence D N I W WN G GN unit unitN O ON P PN f H)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (simulationSentence D N I W WN G GN unit unitN O ON P PN f H)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbeSimulation.endpointLaws_semantics hM,
    ConstructionCellGeneration.generated_semantics hM,
    equivalence_semantics hM]
  exact simulation_equiv hM

theorem simulation_kernel_certificate {m : Nat} (D N I W WN G GN unit unitN O ON P PN f H : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (simulationSentence D N I W WN G GN unit unitN O ON P PN f H)) :=
  ModelTransfer.derives (fun _ hM => simulation_models D N I W WN G GN unit unitN O ON P PN f H hM)

def rangeSentence {m : Nat} (D N W WN V G GN GV unit unitN unitV O ON f H inv g R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo O D W))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo ON N WN))
      (.imp (ConstructionProbePushoutSyntax.hom W WN G GN unit unitN H)
      (.imp (ConstructionProbePushoutSyntax.hom WN W GN G unitN unit inv)
      (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph H inv))
      (.imp (ConstructionProbePushoutSyntax.hom W V G GV unit unitV g)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection g W V))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D f N))
      (.imp (ConstructionProbeMappedPathSyntax.nodeMap O g f)
      (.imp (ConstructionProbePushoutSyntax.squareComm O f H ON)
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W g R))
      (identification WN V GN GV unitN unitV ON inv g R))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      identification_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      ConstructionProbePushoutSyntax.squareComm_freeClosed]

theorem range_models {m : Nat} (D N W WN V G GN GV unit unitN unitV O ON f H inv g R : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (rangeSentence D N W WN V G GN GV unit unitN unitV O ON f H inv g R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (rangeSentence D N W WN V G GN GV unit unitN unitV O ON f H inv g R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),
    ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbePushoutSyntax.squareComm_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    identification_semantics hM]
  exact range_identification hM

theorem range_kernel_certificate {m : Nat} (D N W WN V G GN GV unit unitN unitV O ON f H inv g R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (rangeSentence D N W WN V G GN GV unit unitN unitV O ON f H inv g R)) :=
  ModelTransfer.derives (fun _ hM => range_models D N W WN V G GN GV unit unitN unitV O ON f H inv g R hM)

def probeSentence {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w))
      (.imp (ConstructionProbePushoutSyntax.presentation w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
      (.imp (ConstructionProbePushoutSyntax.presentation w zero N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON)
      (.imp (ConstructionProbePushoutSyntax.hom W WN G GN unit unitN H)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection H W WN))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D f N))
      (.imp (ConstructionProbeSimulation.endpointLaws f H O ON P PN)
      (equivalence W WN G GN unit unitN H))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      equivalence_freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isInductive,
      Project.Formula.isSuccessor,
      Project.Formula.isEmpty,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbeSimulation.endpointLaws_freeClosed,
      ConstructionProbePushoutSyntax.presentation_freeClosed]

theorem probe_models {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbeSimulation.endpointLaws_semantics hM,
    ConstructionProbePushoutSyntax.presentation_semantics hM,
    equivalence_semantics hM]
  exact probe_equiv hM

theorem probe_kernel_certificate {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H)) :=
  ModelTransfer.derives (fun _ hM => probe_models w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O N mulN eN aN bN dN nodeN factorN terminalN targetN LN CN projectionN IN actN EN WN unitN GN KN PN ON f H hM)

def mergerSentence {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w))
      (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots)
      (.imp (ConstructionMergerPushout.presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W G unit))
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid WN GN unitN))
      (.imp (ConstructionProbePushoutSyntax.hom W WN G GN unit unitN H)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection H W WN))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D f N))
      (.imp (ConstructionProbePushoutSyntax.squareComm O f H ON)
      (.imp (ConstructionProbeMappedPathSyntax.nodeMap roots H rootsN)
      (equivalence W WN G GN unit unitN H)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      equivalence_freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isInductive,
      Project.Formula.isSuccessor,
      Project.Formula.isEmpty,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      ConstructionProbePushoutSyntax.squareComm_freeClosed,
      ConstructionMergerPushout.presentation_freeClosed]

theorem merger_models {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbePushoutSyntax.squareComm_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionMergerPushout.presentation_semantics hM,
    equivalence_semantics hM]
  exact merger_equiv hM

theorem merger_kernel_certificate {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H)) :=
  ModelTransfer.derives (fun _ hM => merger_models w n zero D mul e P C L projection A W T B G unit O roots N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f H hM)

end PPAC.Migration.ConstructionCellSimulationEquiv
