/- Pinned SymmetricNames.collectRaw/mem_collectRaw/edge_collectRaw/isName_collectRaw.
The index family is an internal set graph f over J; R tests index/condition.
The exact range is separated from an existing coordinate bound times P.
No external Small/choice function or new collection principle is assumed. -/
import PPAC.Migration.ForcingCohenCoordinates
import PPAC.Migration.ForcingNameConjugacy

namespace PPAC.Migration.ForcingCollectedName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ReplacementPredicates (paramsUp rel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def admissible {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m)
    (J f P child p : Fin m) : Formula m :=
  (Formula.mem p P).conj (.ex ((Formula.mem (Fin.last m) J.castSucc).conj
    ((Source.SetLanguage.edge f.castSucc (Fin.last m) child.castSucc).conj
      (rel R (paramsUp rho) (Fin.last m) p.castSucc))))

def Admissible {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (J f P child p : M.Carrier .set) : Prop :=
  (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧ ∃ i,
    (Definitional.Project.FirstOrderSemantics.reduct M).mem i J ∧
    PureKuratowski.PairMember M i child f ∧ MapRel R env i p

theorem admissible_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (J f P child p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (admissible R rho J f P child p) ↔
      Admissible R (fun i => v (rho i)) (v J) (v f) (v P) (v child) (v p) := by
  simp only [admissible,Admissible,Formula.Realize,KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]

def entry {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (J f P z : Fin m) : Formula m :=
  .ex (.ex ((admissible R (paramsUp (paramsUp rho)) J.castSucc.castSucc f.castSucc.castSucc
    P.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

def Entry {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (J f P z : M.Carrier .set) : Prop :=
  ∃ child p, Admissible R env J f P child p ∧ PureKuratowski.Code M z child p

theorem entry_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (J f P z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entry R rho J f P z) ↔
      Entry R (fun i => v (rho i)) (v J) (v f) (v P) (v z) := by
  simp only [entry,Entry,Formula.Realize,admissible_semantics (M := M),KuratowskiZF.source_code,
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def collected {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (J f P name : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) name.castSucc).iff
    (entry R (paramsUp rho) J.castSucc f.castSucc P.castSucc (Fin.last m)))

def Collected {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (J f P name : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z name ↔ Entry R env J f P z

theorem collected_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (J f P name : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (collected R rho J f P name) ↔
      Collected R (fun i => v (rho i)) (v J) (v f) (v P) (v name) := by
  simp only [collected,Collected,Source.Formula.iff,Formula.Realize,entry_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h z => ⟨(h z).1,(h z).2⟩,fun h z => ⟨(h z).mp,(h z).mpr⟩⟩

theorem exists_collected (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (J f P : M.Carrier .set) :
    ∃ name, Collected R env J f P name := by
  obtain ⟨bound,hbound⟩ := ForcingMapConditions.coordinate_bound hM f
  obtain ⟨product,hproduct⟩ := ForcingCohenCoordinates.exists_cartesian hM bound P
  let inputs : Fin (n+3) → M.Carrier .set := Fin.lastCases P (Fin.lastCases f (Fin.lastCases J env))
  let query := entry R (fun i => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc
    (Fin.last (n+2)).castSucc (Fin.last (n+3))
  have hq : ∀ z, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases z inputs) query ↔ Entry R env J f P z := by
    intro z
    simpa only [inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      (entry_semantics (M := M) (Fin.lastCases z inputs) R
        (fun i => i.castSucc.castSucc.castSucc.castSucc) (Fin.last n).castSucc.castSucc.castSucc
        (Fin.last (n+1)).castSucc.castSucc (Fin.last (n+2)).castSucc (Fin.last (n+3)))
  have hsep := (GodelDefOutput.separation_semantics (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨name,hn⟩ := hsep inputs product
  refine ⟨name,fun z => ?_⟩
  constructor
  · exact fun hz => (hq z).mp ((hn z).mp hz).2
  · intro hz
    obtain ⟨child,p,⟨hp,i,hi,hf,hR⟩,hc⟩ := hz
    exact (hn z).mpr ⟨(hproduct z).mpr ⟨child,(hbound i child hf).2,p,hp,hc⟩,
      (hq z).mpr ⟨child,p,⟨hp,i,hi,hf,hR⟩,hc⟩⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {J f P a b : M.Carrier .set}
    (ha : Collected R env J f P a) (hb : Collected R env J f P b) : a = b :=
  (ModelTransfer.extensionality hM).eq_of_same_members a b (fun z => (ha z).trans (hb z).symm)

theorem edge_collected (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {J f P name : M.Carrier .set}
    (hn : Collected R env J f P name) (child p : M.Carrier .set) :
    PureKuratowski.PairMember M child p name ↔ Admissible R env J f P child p := by
  constructor
  · rintro ⟨z,hc,hz⟩
    obtain ⟨other,q,ha,hc'⟩ := (hn z).mp hz
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hc'
    exact ha
  · intro ha
    obtain ⟨z,hc⟩ := KuratowskiZF.exists_code hM child p
    exact ⟨z,hc,(hn z).mpr ⟨child,p,ha,hc⟩⟩

theorem isName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {J f P name : M.Carrier .set}
    (hn : Collected R env J f P name)
    (hf : ∀ i child, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
      PureKuratowski.PairMember M i child f → ForcingNames.IsName P child) : ForcingNames.IsName P name := by
  apply ForcingNames.intro_name hM P name
  intro z hz
  obtain ⟨child,p,⟨hp,i,hi,hic,hR⟩,hc⟩ := (hn z).mp hz
  exact ⟨child,p,hc,hp,hf i child hi hic⟩

def existenceSentence {n : Nat} (R : Formula (n+2)) (J f P : Fin n) : Source.Sentence :=
  (Formula.ex (collected R (paramsUp id) J.castSucc f.castSucc P.castSucc (Fin.last n))).close

theorem existence_models {n : Nat} (R : Formula (n+2)) (J f P : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) : (Translation.sentence (existenceSentence R J f P)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨name,hn⟩ := exists_collected hM R env (env J) (env f) (env P)
  refine ⟨name,?_⟩
  apply (collected_semantics (M := M) (Fin.lastCases name env) R (paramsUp id)
    J.castSucc f.castSucc P.castSucc (Fin.last n)).mpr
  simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using hn

theorem existence_kernel_certificate {n : Nat} (R : Formula (n+2)) (J f P : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence R J f P)) :=
  ModelTransfer.derives (fun _ hM => existence_models R J f P hM)

end PPAC.Migration.ForcingCollectedName
