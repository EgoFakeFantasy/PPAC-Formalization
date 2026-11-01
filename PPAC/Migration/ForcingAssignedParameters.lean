/- Fixed OrbitAssignments.Assigned: materialize all sixteen actual functions from
ONE full-orbit record function. Existing roots/chains are retained literally.
All other fields use the native unique definable-function constructor, and the
actual Germs contract follows from the SAME concrete selector record. -/
import PPAC.Migration.ForcingAssignedParameterFields

namespace PPAC.Migration.ForcingAssignedParameters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingAssignedParameterFields
open ForcingConditionGraphs (FunctionOn function_unique function_input)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def familyEnv (Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : M.Carrier .set) : Fin 16 → M.Carrier .set := fun j =>
  match j.val with
  | 0 => Roots
  | 1 => Chains
  | 2 => Codes
  | 3 => Orders
  | 4 => Ranks
  | 5 => Selections
  | 6 => Bounds
  | 7 => Labels
  | 8 => Tables
  | 9 => Diagrams
  | 10 => Germs
  | 11 => Quotients
  | 12 => Nonidentities
  | 13 => Highs
  | 14 => Detectors
  | _ => PatternOrders

def Projections (high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : M.Carrier .set) : Prop :=
  Projection 0 high Q records Roots ∧
  Projection 1 high Q records Chains ∧
  Projection 2 high Q records Codes ∧
  Projection 3 high Q records Orders ∧
  Projection 4 high Q records Ranks ∧
  Projection 5 high Q records Selections ∧
  Projection 6 high Q records Bounds ∧
  Projection 7 high Q records Labels ∧
  Projection 8 high Q records Tables ∧
  Projection 9 high Q records Diagrams ∧
  Projection 10 high Q records Germs ∧
  Projection 11 high Q records Quotients ∧
  Projection 12 high Q records Nonidentities ∧
  Projection 13 high Q records Highs ∧
  Projection 14 high Q records Detectors ∧
  Projection 15 high Q records PatternOrders

def projections {m : Nat} (high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : Fin m) : Project.Formula 1 m :=
  (.conj (projection 0 high Q records Roots)
    (.conj (projection 1 high Q records Chains)
    (.conj (projection 2 high Q records Codes)
    (.conj (projection 3 high Q records Orders)
    (.conj (projection 4 high Q records Ranks)
    (.conj (projection 5 high Q records Selections)
    (.conj (projection 6 high Q records Bounds)
    (.conj (projection 7 high Q records Labels)
    (.conj (projection 8 high Q records Tables)
    (.conj (projection 9 high Q records Diagrams)
    (.conj (projection 10 high Q records Germs)
    (.conj (projection 11 high Q records Quotients)
    (.conj (projection 12 high Q records Nonidentities)
    (.conj (projection 13 high Q records Highs)
    (.conj (projection 14 high Q records Detectors)
    (projection 15 high Q records PatternOrders))))))))))))))))

theorem projections_freeClosed {m : Nat} (high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : Fin m) :
    (projections high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders).FreeClosed := by
  simp -implicitDefEqProofs [projections,Definitional.Formula.FreeClosed,projection_freeClosed]

theorem projections_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : Fin m) :
    Project.Formula.satisfies env (projections high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders) ↔
      Projections (env.bound high) (env.bound Q) (env.bound records) (env.bound Roots) (env.bound Chains) (env.bound Codes) (env.bound Orders) (env.bound Ranks) (env.bound Selections) (env.bound Bounds) (env.bound Labels) (env.bound Tables) (env.bound Diagrams) (env.bound Germs) (env.bound Quotients) (env.bound Nonidentities) (env.bound Highs) (env.bound Detectors) (env.bound PatternOrders) := by
  simp only [projections,Projections,Project.Formula.satisfies_conj_iff,projection_semantics hM]

theorem functions {high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : M.Carrier .set}
    (h : Projections high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders) :
    ForcingAssigned.Functions (familyEnv Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders) id Q := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := h
  exact ⟨h0.1,h1.1,h2.1,h3.1,h4.1,h5.1,h6.1,h7.1,h8.1,h9.1,h10.1,h11.1,h12.1,h13.1,h14.1,h15.1⟩

theorem fields_of_record {high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders a output root chain r index U labelSet codes order group support fixing ranks selection rankBound tab germGroup quotient projection reps N X detector J patternCarrier patternOrder selectorDomain selector packA packB packC : M.Carrier .set}
    (hRecords : FunctionOn Q records) (hOutput : PureKuratowski.PairMember M a output records)
    (h : Projections high Q records Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders)
    (hA : ConstructionRoundSelection.Pack root chain r index U labelSet codes order group packA)
    (hB : ConstructionRoundSelection.Pack support fixing ranks selection rankBound tab germGroup quotient projection packB)
    (hC : ConstructionRoundSelection.Pack reps N X detector J patternCarrier patternOrder selectorDomain selector packC)
    (hCode : ConstructionComponentCarrier.Code output packA packB packC) :
    ForcingAssigned.Fields (familyEnv Roots Chains Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders) id a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient N high detector patternOrder := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := h
  have hv (j : Fin 16) := value_intro j high output root chain r index U labelSet codes order group support fixing ranks selection rankBound tab germGroup quotient projection reps N X detector J patternCarrier patternOrder selectorDomain selector packA packB packC hA hB hC hCode
  have ha := function_input hRecords hOutput
  exact ⟨(h0.2 a _).mpr ⟨ha,output,hOutput,hv 0⟩,(h1.2 a _).mpr ⟨ha,output,hOutput,hv 1⟩,(h2.2 a _).mpr ⟨ha,output,hOutput,hv 2⟩,(h3.2 a _).mpr ⟨ha,output,hOutput,hv 3⟩,(h4.2 a _).mpr ⟨ha,output,hOutput,hv 4⟩,(h5.2 a _).mpr ⟨ha,output,hOutput,hv 5⟩,(h6.2 a _).mpr ⟨ha,output,hOutput,hv 6⟩,(h7.2 a _).mpr ⟨ha,output,hOutput,hv 7⟩,(h8.2 a _).mpr ⟨ha,output,hOutput,hv 8⟩,(h9.2 a _).mpr ⟨ha,output,hOutput,hv 9⟩,(h10.2 a _).mpr ⟨ha,output,hOutput,hv 10⟩,(h11.2 a _).mpr ⟨ha,output,hOutput,hv 11⟩,(h12.2 a _).mpr ⟨ha,output,hOutput,hv 12⟩,(h13.2 a _).mpr ⟨ha,output,hOutput,hv 13⟩,(h14.2 a _).mpr ⟨ha,output,hOutput,hv 14⟩,(h15.2 a _).mpr ⟨ha,output,hOutput,hv 15⟩⟩

theorem germs (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient : Fin k)
    {records Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders : M.Carrier .set}
    (hFamily : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records)
    (h : Projections (env high) (env orbitQuotient) records (env reps) (env chains) Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders) :
    ForcingAssigned.Germs (env (rho 0)) (env I) (env mul) (env q) (env reps) Germs := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := h
  intro a root' germ' hRoot' hGerm'
  have ha := function_input h0.1 hRoot'
  obtain ⟨output,hOutput,_⟩ := hFamily.1.2 a ha
  obtain ⟨root,chain,hRoot,_,hRecord⟩ := hFamily.2 a output hOutput
  obtain ⟨r,index,U,labelSet,codes,order,group,support,fixing,ranks,selection,rankBound,tab,germGroup,quotient,projection,reps,N,X,detector,J,patternCarrier,patternOrder,selectorDomain,selector,packA,packB,packC,hA,hB,hC,hCode,_,_,_,hSelector⟩ := hRecord
  have hv := value_intro (M := M) 10 (env high) output root chain r index U labelSet codes order group support fixing ranks selection rankBound tab germGroup quotient projection reps N X detector J patternCarrier patternOrder selectorDomain selector packA packB packC hA hB hC hCode
  have hGerm := (h10.2 a germGroup).mpr ⟨ha,output,hOutput,hv⟩
  have eRoot := function_unique h0.1 hRoot hRoot'
  have eGerm := function_unique h10.1 hGerm hGerm'
  have hCarrier : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) root germGroup := hSelector.1.1
  simpa only [eRoot,eGerm] using hCarrier

theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient : Fin k)
    {records : M.Carrier .set}
    (hFamily : ForcingOrbitParameterFamily.Family hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records)
    (hReps : FunctionOn (env orbitQuotient) (env reps)) (hChains : FunctionOn (env orbitQuotient) (env chains)) :
    ∃ Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders,
      Projections (env high) (env orbitQuotient) records (env reps) (env chains) Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders ∧
      ForcingAssigned.Germs (env (rho 0)) (env I) (env mul) (env q) (env reps) Germs := by
  obtain ⟨h0,h1⟩ := existing_projections hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily hReps hChains
  obtain ⟨Codes,h2⟩ := exists_projection hM 2 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Orders,h3⟩ := exists_projection hM 3 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Ranks,h4⟩ := exists_projection hM 4 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Selections,h5⟩ := exists_projection hM 5 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Bounds,h6⟩ := exists_projection hM 6 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Labels,h7⟩ := exists_projection hM 7 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Tables,h8⟩ := exists_projection hM 8 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Diagrams,h9⟩ := exists_projection hM 9 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Germs,h10⟩ := exists_projection hM 10 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Quotients,h11⟩ := exists_projection hM 11 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Nonidentities,h12⟩ := exists_projection hM 12 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Highs,h13⟩ := exists_projection hM 13 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨Detectors,h14⟩ := exists_projection hM 14 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  obtain ⟨PatternOrders,h15⟩ := exists_projection hM 15 env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily
  have hProjections : Projections (env high) (env orbitQuotient) records (env reps) (env chains) Codes Orders Ranks Selections Bounds Labels Tables Diagrams Germs Quotients Nonidentities Highs Detectors PatternOrders :=
    ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩
  exact ⟨Codes,Orders,Ranks,Selections,Bounds,Labels,Tables,Diagrams,Germs,Quotients,Nonidentities,Highs,Detectors,PatternOrders,hProjections,germs hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient hFamily hProjections⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+14) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    Project.Formula.forallClosure k (.imp (ForcingOrbitParameterFamily.family rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient id records)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn reps orbitQuotient))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn chains orbitQuotient))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj (projections (up high) (up orbitQuotient) (up records) (up reps) (up chains) 13 12 11 10 9 8 7 6 5 4 3 2 1 0)
    (ForcingAssigned.germs (up (rho 0)) (up I) (up mul) (up q) (up reps) 5))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingOrbitParameterFamily.family_freeClosed,projections_freeClosed,ForcingAssigned.germs_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,ForcingOrbitParameterFamily.family_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),projections_semantics hM,ForcingAssigned.germs_semantics hM]
  exact construct hM env rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models rho I K B w G F mul q bound labels E zero names high objects maps reps chains orbitQuotient records hM

end PPAC.Migration.ForcingAssignedParameters
