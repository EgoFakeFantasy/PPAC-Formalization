/- Pinned ProductNames.system uses Equiv.Perm I; SupportFilter.Fix uses
pointwise stabilizers of label sets. Construct their actual internal carriers
from the donor function space and Separation, without assuming a group set. -/
import PPAC.Migration.ForcingNameConjugacy
import YesMetaZFC.SetTheory.FunctionSpaceConstruction
import PPAC.Migration.RestrictionSyntax

namespace PPAC.Migration.ForcingLabelPermutations
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingConditionGraphs
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem subset_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I J : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (Source.SetLanguage.subset I J) ↔
      ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x (env I) →
        (Definitional.Project.FirstOrderSemantics.reduct M).mem x (env J) := by
  simp only [RestrictionSyntax.subset_original,RestrictionSyntax.subset,Formula.Realize,
    Fin.lastCases_last,Fin.lastCases_castSucc]

def Carrier (I G : M.Carrier .set) : Prop :=
  ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r G ↔ Permutation I r

def carrier {m : Nat} (I G : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) G.castSucc).iff (permutation I.castSucc (Fin.last m)))

theorem carrier_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I G : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (carrier I G) ↔ Carrier (env I) (env G) := by
  simp only [carrier,Carrier,Source.Formula.iff,Formula.Realize,permutation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h r => ⟨(h r).1,(h r).2⟩,fun h r => ⟨(h r).mp,(h r).mpr⟩⟩

/-- Reuse the completed native function-space theorem, then separate bijections. -/
theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (I : M.Carrier .set) :
    ∃ G, Carrier I G := by
  obtain ⟨space,hSpace⟩ := SetTheory.ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) I I
  let query := permutation (0 : Fin 2) 1
  have sep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨G,hG⟩ := sep (fun _ => I) space
  have hq : ∀ r, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases r (fun _ : Fin 1 => I)) query ↔ Permutation I r := by
    intro r
    exact permutation_semantics _ (0 : Fin 2) 1
  refine ⟨G,fun r => ?_⟩
  constructor
  · intro hr
    exact (hq r).mp ((hG r).mp hr).2
  · intro hr
    exact (hG r).mpr ⟨(hSpace r).mpr ((native_endomap hM I r).mp hr.1),(hq r).mpr hr⟩

theorem carrier_unique (hM : FirstOrder.Theory.Models M nativeZF) {I G H : M.Carrier .set}
    (hG : Carrier I G) (hH : Carrier I H) : G = H :=
  (ModelTransfer.extensionality hM).eq_of_same_members G H (fun r => (hG r).trans (hH r).symm)

theorem identity_mem (hM : FirstOrder.Theory.Models M nativeZF) {I G : M.Carrier .set} (hG : Carrier I G) :
    ∃ e, (Definitional.Project.FirstOrderSemantics.reduct M).mem e G ∧ IdentityGraph I e := by
  obtain ⟨e,he,hi⟩ := exists_identity hM I
  exact ⟨e,(hG e).mpr he,hi⟩

theorem inverse_mem (hM : FirstOrder.Theory.Models M nativeZF) {I G r : M.Carrier .set}
    (hG : Carrier I G) (hr : (Definitional.Project.FirstOrderSemantics.reduct M).mem r G) :
    ∃ i, (Definitional.Project.FirstOrderSemantics.reduct M).mem i G ∧ InverseGraph r i := by
  obtain ⟨i,hi,hri⟩ := exists_inverse hM ((hG r).mp hr)
  exact ⟨i,(hG i).mpr hi,hri⟩

theorem composition_mem (hM : FirstOrder.Theory.Models M nativeZF) {I G r s : M.Carrier .set}
    (hG : Carrier I G) (hr : (Definitional.Project.FirstOrderSemantics.reduct M).mem r G)
    (hs : (Definitional.Project.FirstOrderSemantics.reduct M).mem s G) :
    ∃ t, (Definitional.Project.FirstOrderSemantics.reduct M).mem t G ∧ CompositionGraph I r s t := by
  obtain ⟨t,ht,hc⟩ := exists_composition hM ((hG r).mp hr) ((hG s).mp hs)
  exact ⟨t,(hG t).mpr ht,hc⟩

def Fixes (J r : M.Carrier .set) : Prop :=
  ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J → PureKuratowski.PairMember M x x r

def fixes {m : Nat} (J r : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) J.castSucc).imp (Source.SetLanguage.edge r.castSucc (Fin.last m) (Fin.last m)))

theorem fixes_semantics {m : Nat} (env : Fin m → M.Carrier .set) (J r : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (fixes J r) ↔ Fixes (env J) (env r) := by
  simp only [fixes,Fixes,Formula.Realize,KuratowskiZF.source_edge,Fin.lastCases_last,Fin.lastCases_castSucc]

def Fixing (G J K : M.Carrier .set) : Prop :=
  ∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r K ↔
    (Definitional.Project.FirstOrderSemantics.reduct M).mem r G ∧ Fixes J r

def fixing {m : Nat} (G J K : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) K.castSucc).iff
    ((Formula.mem (Fin.last m) G.castSucc).conj (fixes J.castSucc (Fin.last m))))

theorem fixing_semantics {m : Nat} (env : Fin m → M.Carrier .set) (G J K : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (fixing G J K) ↔
      Fixing (env G) (env J) (env K) := by
  simp only [fixing,Fixing,Source.Formula.iff,Formula.Realize,fixes_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h r => ⟨(h r).1,(h r).2⟩,fun h r => ⟨(h r).mp,(h r).mpr⟩⟩

theorem exists_fixing (hM : FirstOrder.Theory.Models M nativeZF) (G J : M.Carrier .set) :
    ∃ K, Fixing G J K := by
  let query := fixes (0 : Fin 2) 1
  have sep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨K,hK⟩ := sep (fun _ => J) G
  refine ⟨K,fun r => (hK r).trans (and_congr Iff.rfl ?_)⟩
  exact fixes_semantics _ (0 : Fin 2) 1

theorem fixing_unique (hM : FirstOrder.Theory.Models M nativeZF) {G J K L : M.Carrier .set}
    (hK : Fixing G J K) (hL : Fixing G J L) : K = L :=
  (ModelTransfer.extensionality hM).eq_of_same_members K L (fun r => (hK r).trans (hL r).symm)

theorem fixes_identity {I J e : M.Carrier .set}
    (hJI : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x I) (he : IdentityGraph I e) : Fixes J e :=
  fun x hx => (he x x).mpr ⟨hJI x hx,rfl⟩

theorem fixes_inverse {J r i : M.Carrier .set} (hri : InverseGraph r i) (hr : Fixes J r) : Fixes J i :=
  fun x hx => (hri x x).mp (hr x hx)

theorem fixes_composition {I J r s t : M.Carrier .set} (hs : FunctionOn I s)
    (hc : CompositionGraph I r s t) (hr : Fixes J r) (ht : Fixes J s) : Fixes J t :=
  fun x hx => (hc x x).mpr ⟨function_input hs (ht x hx),x,ht x hx,hr x hx⟩

/-- The source pointwise stabilizer is closed under the actual internal operations. -/
theorem fixing_closed (hM : FirstOrder.Theory.Models M nativeZF) {I G J K : M.Carrier .set}
    (hG : Carrier I G) (hK : Fixing G J K)
    (hJI : ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x J →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem x I) :
    (∃ e, (Definitional.Project.FirstOrderSemantics.reduct M).mem e K ∧ IdentityGraph I e) ∧
    (∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r K →
      ∃ i, (Definitional.Project.FirstOrderSemantics.reduct M).mem i K ∧ InverseGraph r i) ∧
    (∀ r s, (Definitional.Project.FirstOrderSemantics.reduct M).mem r K →
      (Definitional.Project.FirstOrderSemantics.reduct M).mem s K →
      ∃ t, (Definitional.Project.FirstOrderSemantics.reduct M).mem t K ∧ CompositionGraph I r s t) := by
  refine ⟨?_,?_,?_⟩
  · obtain ⟨e,he,hi⟩ := identity_mem hM hG
    exact ⟨e,(hK e).mpr ⟨he,fixes_identity hJI hi⟩,hi⟩
  · intro r hr
    obtain ⟨hrG,hrJ⟩ := (hK r).mp hr
    obtain ⟨i,hi,hri⟩ := inverse_mem hM hG hrG
    exact ⟨i,(hK i).mpr ⟨hi,fixes_inverse hri hrJ⟩,hri⟩
  · intro r s hr hs
    obtain ⟨hrG,hrJ⟩ := (hK r).mp hr
    obtain ⟨hsG,hsJ⟩ := (hK s).mp hs
    obtain ⟨t,ht,hc⟩ := composition_mem hM hG hrG hsG
    exact ⟨t,(hK t).mpr ⟨ht,fixes_composition ((hG s).mp hsG).1.1 hc hrJ hsJ⟩,hc⟩

/-- Existential closure under the source group's actual graph operations. -/
def closed {m : Nat} (I K : Fin m) : Formula m :=
  (Formula.ex ((Formula.mem (Fin.last m) K.castSucc).conj (identityGraph I.castSucc (Fin.last m)))).conj
    ((Formula.all ((Formula.mem (Fin.last m) K.castSucc).imp (.ex
      ((Formula.mem (Fin.last (m+1)) K.castSucc.castSucc).conj
        (inverseGraph (Fin.last m).castSucc (Fin.last (m+1))))))).conj
      (.all (.all ((Formula.mem (Fin.last m).castSucc K.castSucc.castSucc).imp
        ((Formula.mem (Fin.last (m+1)) K.castSucc.castSucc).imp (.ex
          ((Formula.mem (Fin.last (m+2)) K.castSucc.castSucc.castSucc).conj
            (compositionGraph I.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
              (Fin.last (m+1)).castSucc (Fin.last (m+2))))))))))

theorem closed_semantics {m : Nat} (env : Fin m → M.Carrier .set) (I K : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem env (closed I K) ↔
      (∃ e, (Definitional.Project.FirstOrderSemantics.reduct M).mem e (env K) ∧ IdentityGraph (env I) e) ∧
      (∀ r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env K) →
        ∃ i, (Definitional.Project.FirstOrderSemantics.reduct M).mem i (env K) ∧ InverseGraph r i) ∧
      (∀ r s, (Definitional.Project.FirstOrderSemantics.reduct M).mem r (env K) →
        (Definitional.Project.FirstOrderSemantics.reduct M).mem s (env K) →
        ∃ t, (Definitional.Project.FirstOrderSemantics.reduct M).mem t (env K) ∧ CompositionGraph (env I) r s t) := by
  simp only [closed,Formula.Realize,identityGraph_semantics (M := M),inverseGraph_semantics (M := M),
    compositionGraph_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]

def closedSentence : Source.Sentence := ((carrier (0 : Fin 4) 1).imp ((fixing 1 2 3).imp
  ((Source.SetLanguage.subset 2 0).imp (closed 0 3)))).close

theorem closed_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence closedSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hG hK hJI
  exact (closed_semantics (M := M) env 0 3).mpr
    (fixing_closed hM ((carrier_semantics (M := M) env 0 1).mp hG)
      ((fixing_semantics (M := M) env 1 2 3).mp hK)
      ((subset_semantics env 2 0).mp hJI))

theorem closed_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence closedSentence) :=
  ModelTransfer.derives (fun _ hM => closed_models hM)

def carrierSentence : Source.Sentence := (Formula.ex (carrier (0 : Fin 2) 1)).close

def fixingSentence : Source.Sentence := (Formula.ex (fixing (0 : Fin 3) 1 2)).close

theorem carrier_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence carrierSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨G,hG⟩ := exists_carrier hM (env 0)
  refine ⟨G, ?_⟩
  apply (carrier_semantics (M := M) (Fin.lastCases G env) (0 : Fin 1).castSucc (Fin.last 1)).mpr
  simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using hG

theorem fixing_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence fixingSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨K,hK⟩ := exists_fixing hM (env 0) (env 1)
  refine ⟨K, ?_⟩
  apply (fixing_semantics (M := M) (Fin.lastCases K env) (0 : Fin 2).castSucc (1 : Fin 2).castSucc (Fin.last 2)).mpr
  simpa only [Fin.lastCases_castSucc,Fin.lastCases_last] using hK

theorem carrier_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence carrierSentence) :=
  ModelTransfer.derives (fun _ hM => carrier_models hM)

theorem fixing_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence fixingSentence) :=
  ModelTransfer.derives (fun _ hM => fixing_models hM)

end PPAC.Migration.ForcingLabelPermutations
