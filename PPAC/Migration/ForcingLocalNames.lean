/- Pinned Models/LocalQuotients.lean:287-323, LocalName and its literal
restriction maps. Reuse PowerName.Candidates, native Separation, and the
existing exact identity graph; no new rank bound or replacement name type. -/
import PPAC.Migration.ForcingLabelBound

namespace PPAC.Migration.ForcingLocalNames
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportedNames (Supported)
open ForcingLabelPermutations (Fixing)
open ForcingConditionGraphs (IdentityGraph CompositionGraph)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact source PowerCandidate subtype predicate, at the supplied actual bound
and pointwise stabilizer. Every internal name is quantified. -/
def LocalName (v : Fin 7 → M.Carrier .set) (G F B H nu : M.Carrier .set) : Prop :=
  (ForcingHS.HS ForcingProductFamily.actionFormula v G (v 6) F nu ∧
    ForcingPowerName.Subset nu B) ∧ Supported v H nu

def localName {k : Nat} (rho : Fin 7 → Fin k) (G F B H nu : Fin k) : Formula k :=
  (ForcingPowerName.candidate rho G F B nu).conj (ForcingEquivariantMix.fixedAll rho H nu)

theorem localName_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F B H nu : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (localName rho G F B H nu) ↔
      LocalName (fun j => env (rho j)) (env G) (env F) (env B) (env H) (env nu) := by
  simp only [localName,LocalName,Formula.Realize,ForcingPowerName.candidate_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M)]

def Carrier (v : Fin 7 → M.Carrier .set) (G F B H X : M.Carrier .set) : Prop :=
  ∀ nu, (Project.FirstOrderSemantics.reduct M).mem nu X ↔ LocalName v G F B H nu

def carrier {k : Nat} (rho : Fin 7 → Fin k) (G F B H X : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) X.castSucc).iff
    (localName (paramsUp rho) G.castSucc F.castSucc B.castSucc H.castSucc (Fin.last k)))

theorem carrier_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → Fin k) (G F B H X : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (carrier rho G F B H X) ↔
      Carrier (fun j => env (rho j)) (env G) (env F) (env B) (env H) (env X) := by
  simp only [carrier,Carrier,Source.Formula.iff,Formula.Realize,localName_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1,(h x).2⟩,fun h x => ⟨(h x).mp,(h x).mpr⟩⟩

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF)
    (v : Fin 7 → M.Carrier .set) (G F B H : M.Carrier .set) :
    ∃ X, Carrier v G F B H X := by
  obtain ⟨C,hC⟩ := ForcingPowerName.exists_candidates hM v G F B
  let env : Fin 8 → M.Carrier .set := Fin.lastCases H v
  let rho : Fin 7 → Fin 8 := Fin.castSucc
  let query := ForcingEquivariantMix.fixedAll (paramsUp rho) (Fin.last 7).castSucc (Fin.last 8)
  have hq : ∀ nu, Formula.Realize (Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases nu env) query ↔ Supported v H nu := by
    intro nu
    simpa only [query,env,rho,paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using
      ForcingSupportedNames.supported_semantics (M := M) (Fin.lastCases nu env)
        (paramsUp rho) (Fin.last 7).castSucc (Fin.last 8)
  have hsep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨X,hX⟩ := hsep env C
  exact ⟨X,fun nu => (hX nu).trans (and_congr (hC nu) (hq nu))⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {G F B H X Y : M.Carrier .set}
    (hX : Carrier v G F B H X) (hY : Carrier v G F B H Y) : X = Y :=
  (ModelTransfer.extensionality hM).eq_of_same_members X Y (fun nu => (hX nu).trans (hY nu).symm)

/-- Source restrict_name: the same raw name belongs to the target carrier. -/
theorem restrict_name {v : Fin 7 → M.Carrier .set} {G F B J K HJ HK X Y : M.Carrier .set}
    (hJ : Fixing G J HJ) (hK : Fixing G K HK) (hJK : ForcingPowerName.Subset J K)
    (hX : Carrier v G F B HJ X) (hY : Carrier v G F B HK Y) :
    ForcingPowerName.Subset X Y := by
  intro nu hn
  obtain ⟨hc,hs⟩ := (hX nu).mp hn
  exact (hY nu).mpr ⟨hc,ForcingSupportedNames.supported_mono hJ hK hJK hs⟩

/-- The actual ground-set restriction graph, with literal name preservation and
injectivity, is the existing identity graph on the source carrier. -/
theorem exists_restrict (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {G F B J K HJ HK X Y : M.Carrier .set}
    (hJ : Fixing G J HJ) (hK : Fixing G K HK) (hJK : ForcingPowerName.Subset J K)
    (hX : Carrier v G F B HJ X) (hY : Carrier v G F B HK Y) :
    ∃ f, ForcingSupportSize.Injection X Y f ∧ IdentityGraph X f := by
  have hXY := restrict_name hJ hK hJK hX hY
  obtain ⟨f,hf,he⟩ := ForcingConditionGraphs.exists_identity hM X
  exact ⟨f,⟨⟨hf.1.1,fun x y hxy => hXY y (hf.1.2 x y hxy)⟩,hf.2.1⟩,he⟩

/-- Source restrict_restrict, as equality of actual graph composition with the
direct restriction graph; no quotient equality is substituted. -/
theorem restrict_restrict {X Y f g : M.Carrier .set}
    (hXY : ForcingPowerName.Subset X Y) (hf : IdentityGraph X f) (hg : IdentityGraph Y g) :
    CompositionGraph X g f f := by
  intro x z
  constructor
  · intro hxz
    obtain ⟨hx,rfl⟩ := (hf x z).mp hxz
    exact ⟨hx,x,hxz,(hg x x).mpr ⟨hXY x hx,rfl⟩⟩
  · rintro ⟨_,y,hxy,hyz⟩
    obtain ⟨hx,rfl⟩ := (hf x y).mp hxy
    obtain ⟨_,rfl⟩ := (hg x z).mp hyz
    exact (hf x x).mpr ⟨hx,rfl⟩

def existenceSentence {k : Nat} (rho : Fin 7 → Fin k) (G F B H : Fin k) : Source.Sentence :=
  (Formula.ex (carrier (paramsUp rho) G.castSucc F.castSucc B.castSucc H.castSucc (Fin.last k))).close

theorem existence_models {k : Nat} (rho : Fin 7 → Fin k) (G F B H : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence rho G F B H)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨X,hX⟩ := exists_carrier hM (fun j => env (rho j)) (env G) (env F) (env B) (env H)
  refine ⟨X,?_⟩
  apply (carrier_semantics (M := M) (Fin.lastCases X env) (paramsUp rho)
    G.castSucc F.castSucc B.castSucc H.castSucc (Fin.last k)).mpr
  simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc] using hX

theorem existence_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F B H : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence rho G F B H)) :=
  ModelTransfer.derives (fun _ hM => existence_models rho G F B H hM)

def uniquenessSentence {k : Nat} (rho : Fin 7 → Fin k) (G F B H X Y : Fin k) : Source.Sentence :=
  ((carrier rho G F B H X).imp ((carrier rho G F B H Y).imp (.equal X Y))).close

theorem uniqueness_models {k : Nat} (rho : Fin 7 → Fin k) (G F B H X Y : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence rho G F B H X Y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hX hY
  exact unique hM ((carrier_semantics (M := M) env rho G F B H X).mp hX)
    ((carrier_semantics (M := M) env rho G F B H Y).mp hY)

theorem uniqueness_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (G F B H X Y : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence rho G F B H X Y)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models rho G F B H X Y hM)

def restrictionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (G F B J K HJ HK X Y : Fin k) : Source.Sentence :=
  ((ForcingLabelPermutations.fixing G J HJ).imp
    ((ForcingLabelPermutations.fixing G K HK).imp
      ((Source.SetLanguage.subset J K).imp
        ((carrier rho G F B HJ X).imp ((carrier rho G F B HK Y).imp
          (.ex ((Source.SetLanguage.injection (Fin.last k) X.castSucc Y.castSucc).conj
            (ForcingConditionGraphs.identityGraph X.castSucc (Fin.last k))))))))).close

theorem restriction_models {k : Nat} (rho : Fin 7 → Fin k)
    (G F B J K HJ HK X Y : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (restrictionSentence rho G F B J K HJ HK X Y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hJ hK hJK hX hY
  obtain ⟨f,hf,he⟩ := exists_restrict hM
    ((ForcingLabelPermutations.fixing_semantics (M := M) env G J HJ).mp hJ)
    ((ForcingLabelPermutations.fixing_semantics (M := M) env G K HK).mp hK)
    ((ForcingLabelPermutations.subset_semantics (M := M) env J K).mp hJK)
    ((carrier_semantics (M := M) env rho G F B HJ X).mp hX)
    ((carrier_semantics (M := M) env rho G F B HK Y).mp hY)
  refine ⟨f,?_,?_⟩
  · apply (ForcingSupportSize.injection_semantics (M := M) (Fin.lastCases f env)
      (Fin.last k) X.castSucc Y.castSucc).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using hf
  · apply (ForcingConditionGraphs.identityGraph_semantics (M := M) (Fin.lastCases f env)
      X.castSucc (Fin.last k)).mpr
    simpa only [Fin.lastCases_last,Fin.lastCases_castSucc] using he

theorem restriction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (G F B J K HJ HK X Y : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (restrictionSentence rho G F B J K HJ HK X Y)) :=
  ModelTransfer.derives (fun _ hM => restriction_models rho G F B J K HJ HK X Y hM)

def compositionSentence : Source.Sentence :=
  ((Source.SetLanguage.subset (0 : Fin 4) 1).imp
    ((ForcingConditionGraphs.identityGraph 0 2).imp
      ((ForcingConditionGraphs.identityGraph 1 3).imp
        (ForcingConditionGraphs.compositionGraph 0 3 2 2)))).close

theorem composition_models (_hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence compositionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hs hf hg
  exact (ForcingConditionGraphs.compositionGraph_semantics (M := M) env 0 3 2 2).mpr
    (restrict_restrict ((ForcingLabelPermutations.subset_semantics (M := M) env 0 1).mp hs)
      ((ForcingConditionGraphs.identityGraph_semantics (M := M) env 0 2).mp hf)
      ((ForcingConditionGraphs.identityGraph_semantics (M := M) env 1 3).mp hg))

theorem composition_kernel_certificate :
    FirstOrder.Derives nativeZF [] (Translation.sentence compositionSentence) :=
  ModelTransfer.derives (fun _ hM => composition_models hM)

end PPAC.Migration.ForcingLocalNames
