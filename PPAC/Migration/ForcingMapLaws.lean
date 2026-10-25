/- Adapted from pinned OpenAI ForcingNames.lean:130-165.
The source Child induction proofs are replayed through the existing object
formula induction schema. No external WellFounded or new recursion is assumed. -/
import PPAC.Migration.ForcingMapConditions
import PPAC.Migration.ForcingNames

namespace PPAC.Migration.ForcingMapLaws
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
open ForcingMapConditions (MapRel IsFunction Mapped mapping)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Convenience application of the already proved original Child schema. -/
theorem formula_induction (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+1)) (params : Fin n → M.Carrier .set)
    (step : ∀ sigma, (∀ tau condition, PureKuratowski.PairMember M tau condition sigma →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases tau params) p) →
      Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases sigma params) p) :
    ∀ sigma, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases sigma params) p := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  have hi := (GodelDefOutput.close_semantics E _).mp
    ((Translation.realizes_sentence M _).mp
      ((ForcingNameInduction.kernel_certificate p).semantically_entails M hM)) params
  change Formula.Realize E params (ForcingNameInduction.progressive p id) →
    Formula.Realize E params (SetInductionSyntax.holds p id) at hi
  have hAll := hi ((ForcingNameInduction.progressive_semantics params p id).mpr (by
    intro sigma ih
    exact step sigma (fun tau condition he => ih tau ⟨condition, he⟩)))
  exact (ForcingNameInduction.holds_semantics E params p id).mp hAll

def identityRelation (n : Nat) : Formula (n+2) :=
  .equal (Fin.last n).castSucc (Fin.last (n+1))

theorem identity_rel {n : Nat} (params : Fin n → M.Carrier .set) (x y : M.Carrier .set) :
    MapRel (identityRelation n) params x y ↔ x = y := by
  simp only [MapRel, identityRelation, Formula.Realize, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem identity_function {n : Nat} (params : Fin n → M.Carrier .set) :
    IsFunction (identityRelation n) params := by
  intro x
  exact ⟨x, (identity_rel params x x).mpr rfl,
    fun z hz => ((identity_rel params x z).mp hz).symm⟩

def identityAt {n m : Nat} (rho : Fin n → Fin m) (P sigma : Fin m) : Formula m :=
  (ForcingNames.isName P sigma).imp (mapping (identityRelation n) rho sigma sigma)

theorem identityAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (rho : Fin n → Fin m) (P sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (identityAt rho P sigma) ↔
      (ForcingNames.IsName (v P) (v sigma) → Mapped (identityRelation n) (fun i => v (rho i)) (v sigma) (v sigma)) := by
  simp only [identityAt, Formula.Realize, ForcingNames.isName_semantics, ForcingMapConditions.mapping_semantics]

theorem identity_mapping (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (params : Fin n → M.Carrier .set) (P sigma : M.Carrier .set) (hName : ForcingNames.IsName P sigma) :
    Mapped (identityRelation n) params sigma sigma := by
  let inputs : Fin (n+1) → M.Carrier .set := Fin.lastCases P params
  let q := identityAt (fun i : Fin n => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))
  have hq : ∀ s, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases s inputs) q ↔
      (ForcingNames.IsName P s → Mapped (identityRelation n) params s s) := by
    intro s
    simpa only [q, inputs, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (identityAt_semantics (Fin.lastCases s inputs) (fun i : Fin n => i.castSucc.castSucc)
        (Fin.last n).castSucc (Fin.last (n+1)))
  have hf := identity_function params
  have hAll := formula_induction hM q inputs (by
    intro s ih
    apply (hq s).mpr
    intro hn
    obtain ⟨output, hm⟩ := ForcingMapConditions.exists_mapping hM (identityRelation n) params hf s
    have heq : output = s := by
      apply (ModelTransfer.extensionality hM).eq_of_same_members
      intro z
      constructor
      · intro hz
        obtain ⟨tau, condition, v, c, he, hv, hc, hCode⟩ := (ForcingMapConditions.mem_mapping hM hf hm z).mp hz
        have ht := (hq tau).mp (ih tau condition he) (ForcingNames.child_condition hn he).2
        have hvEq := ForcingMapConditions.unique hM hf hv ht
        have hcEq := (identity_rel params condition c).mp hc
        subst v
        subst c
        obtain ⟨old, hOld, hMem⟩ := he
        exact (KuratowskiZF.code_unique hM hOld hCode) ▸ hMem
      · intro hz
        obtain ⟨tau, condition, hCode, _, hTau⟩ := ForcingNames.edges hn z hz
        have he : PureKuratowski.PairMember M tau condition s := ⟨z, hCode, hz⟩
        exact (ForcingMapConditions.mem_mapping hM hf hm z).mpr
          ⟨tau, condition, tau, condition, he, (hq tau).mp (ih tau condition he) hTau,
            (identity_rel params condition condition).mpr rfl, hCode⟩
    exact heq ▸ hm)
  exact (hq sigma).mp (hAll sigma) hName

def identitySentence (n : Nat) : Source.Sentence :=
  (identityAt (fun i : Fin n => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))).close

theorem identity_models (n : Nat) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (identitySentence n)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  apply (identityAt_semantics v _ _ _).mpr
  exact identity_mapping hM _ _ _

theorem identity_kernel_certificate (n : Nat) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (identitySentence n)) :=
  ModelTransfer.derives (fun _ hM => identity_models n hM)

/-- Composition order is the original f after g. -/
def compose {n : Nat} (f g : Formula (n+2)) : Formula (n+2) :=
  .ex ((ReplacementPredicates.rel g (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+2))).conj
      (ReplacementPredicates.rel f (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n+2)) (Fin.last (n+1)).castSucc))

theorem compose_rel {n : Nat} (f g : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (x z : M.Carrier .set) :
    MapRel (compose f g) params x z ↔ ∃ y, MapRel g params x y ∧ MapRel f params y z := by
  change Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
    (Fin.lastCases z (Fin.lastCases x params)) (compose f g) ↔ _
  simp only [compose, Formula.Realize, ForcingMapConditions.rel_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem compose_function {n : Nat} {f g : Formula (n+2)} {params : Fin n → M.Carrier .set}
    (hf : IsFunction f params) (hg : IsFunction g params) : IsFunction (compose f g) params := by
  intro x
  obtain ⟨y, hy, _⟩ := hg x
  obtain ⟨z, hz, _⟩ := hf y
  refine ⟨z, (compose_rel f g params x z).mpr ⟨y, hy, hz⟩, ?_⟩
  intro z' hz'
  obtain ⟨y', hy', hz'⟩ := (compose_rel f g params x z').mp hz'
  have heq := ForcingMapConditions.function_unique hg x y' y hy' hy
  subst y'
  exact ForcingMapConditions.function_unique hf y z' z hz' hz

def compositionAt {n m : Nat} (f g : Formula (n+2)) (rho : Fin n → Fin m) (sigma : Fin m) : Formula m :=
  .all (.all ((mapping g (paramsUp (paramsUp rho)) sigma.castSucc.castSucc (Fin.last m).castSucc).imp
    ((mapping f (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (mapping (compose f g) (paramsUp (paramsUp rho)) sigma.castSucc.castSucc (Fin.last (m+1))))))

theorem compositionAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (f g : Formula (n+2)) (rho : Fin n → Fin m) (sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (compositionAt f g rho sigma) ↔
      ∀ mid output, Mapped g (fun i => v (rho i)) (v sigma) mid →
        Mapped f (fun i => v (rho i)) mid output → Mapped (compose f g) (fun i => v (rho i)) (v sigma) output := by
  simp only [compositionAt, Formula.Realize, ForcingMapConditions.mapping_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem composition_mapping (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f g : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : IsFunction f params) (hg : IsFunction g params)
    {sigma mid output : M.Carrier .set} (hMid : Mapped g params sigma mid) (hOutput : Mapped f params mid output) :
    Mapped (compose f g) params sigma output := by
  let q := compositionAt f g Fin.castSucc (Fin.last n)
  have hq : ∀ s, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases s params) q ↔
      ∀ mid output, Mapped g params s mid → Mapped f params mid output → Mapped (compose f g) params s output := by
    intro s
    simpa only [q, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (compositionAt_semantics (Fin.lastCases s params) f g Fin.castSucc (Fin.last n))
  have hc := compose_function hf hg
  have hAll := formula_induction hM q params (by
    intro s ih
    apply (hq s).mpr
    intro middle result hm hr
    obtain ⟨composed, hh⟩ := ForcingMapConditions.exists_mapping hM (compose f g) params hc s
    have heq : result = composed := by
      apply (ModelTransfer.extensionality hM).eq_of_same_members
      intro z
      constructor
      · intro hz
        obtain ⟨tau, condition, v, c, he, hv, hCondition, hCode⟩ :=
          (ForcingMapConditions.mem_mapping hM hf hr z).mp hz
        obtain ⟨original, p, hOriginal, hG, hp⟩ := (ForcingMapConditions.edge_mapping hM hg hm tau condition).mp he
        exact (ForcingMapConditions.mem_mapping hM hc hh z).mpr
          ⟨original, p, v, c, hOriginal, (hq original).mp (ih original p hOriginal) tau v hG hv,
            (compose_rel f g params p c).mpr ⟨condition, hp, hCondition⟩, hCode⟩
      · intro hz
        obtain ⟨tau, condition, v, c, he, hv, hCondition, hCode⟩ :=
          (ForcingMapConditions.mem_mapping hM hc hh z).mp hz
        obtain ⟨p, hp, hpc⟩ := (compose_rel f g params condition c).mp hCondition
        obtain ⟨t, ht⟩ := ForcingMapConditions.exists_mapping hM g params hg tau
        obtain ⟨w, hw⟩ := ForcingMapConditions.exists_mapping hM f params hf t
        have hvw := ForcingMapConditions.unique hM hc hv ((hq tau).mp (ih tau condition he) t w ht hw)
        exact (ForcingMapConditions.mem_mapping hM hf hr z).mpr
          ⟨t, p, w, c, (ForcingMapConditions.edge_mapping hM hg hm t p).mpr ⟨tau, condition, he, ht, hp⟩,
            hw, hpc, hvw ▸ hCode⟩
    exact heq.symm ▸ hh)
  exact (hq sigma).mp (hAll sigma) mid output hMid hOutput

def compositionSentence {n : Nat} (f g : Formula (n+2)) : Source.Sentence :=
  ((ForcingMapConditions.function f Fin.castSucc).imp
    ((ForcingMapConditions.function g Fin.castSucc).imp (compositionAt f g Fin.castSucc (Fin.last n)))).close

theorem composition_models {n : Nat} (f g : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (compositionSentence f g)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hf hg
  apply (compositionAt_semantics v f g Fin.castSucc (Fin.last n)).mpr
  intro mid output hm ho
  exact composition_mapping hM ((ForcingMapConditions.function_semantics v f Fin.castSucc).mp hf)
    ((ForcingMapConditions.function_semantics v g Fin.castSucc).mp hg) hm ho

theorem composition_kernel_certificate {n : Nat} (f g : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (compositionSentence f g)) :=
  ModelTransfer.derives (fun _ hM => composition_models f g hM)

def mapsInto {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (P Q : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last m).castSucc P.castSucc.castSucc).imp
    ((ReplacementPredicates.rel f (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1))).imp
      (Formula.mem (Fin.last (m+1)) Q.castSucc.castSucc))))

theorem mapsInto_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (f : Formula (n+2)) (rho : Fin n → Fin m) (P Q : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (mapsInto f rho P Q) ↔
      ∀ p q, (Definitional.Project.FirstOrderSemantics.reduct M).mem p (v P) →
        MapRel f (fun i => v (rho i)) p q → (Definitional.Project.FirstOrderSemantics.reduct M).mem q (v Q) := by
  simp only [mapsInto, Formula.Realize, ForcingMapConditions.rel_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def preservesAt {n m : Nat} (f : Formula (n+2)) (rho : Fin n → Fin m) (P Q sigma : Fin m) : Formula m :=
  (ForcingNames.isName P sigma).imp (.all ((mapping f (paramsUp rho) sigma.castSucc (Fin.last m)).imp
    (ForcingNames.isName Q.castSucc (Fin.last m))))

theorem preservesAt_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (f : Formula (n+2)) (rho : Fin n → Fin m) (P Q sigma : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (preservesAt f rho P Q sigma) ↔
      (ForcingNames.IsName (v P) (v sigma) → ∀ output, Mapped f (fun i => v (rho i)) (v sigma) output →
        ForcingNames.IsName (v Q) output) := by
  simp only [preservesAt, Formula.Realize, ForcingNames.isName_semantics,
    ForcingMapConditions.mapping_semantics (M := M), paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem name_preservation (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {f : Formula (n+2)} {params : Fin n → M.Carrier .set} (hf : IsFunction f params)
    (P Q : M.Carrier .set)
    (hInto : ∀ p q, (Definitional.Project.FirstOrderSemantics.reduct M).mem p P →
      MapRel f params p q → (Definitional.Project.FirstOrderSemantics.reduct M).mem q Q)
    {sigma output : M.Carrier .set} (hName : ForcingNames.IsName P sigma) (hm : Mapped f params sigma output) :
    ForcingNames.IsName Q output := by
  let inputs : Fin (n+2) → M.Carrier .set := Fin.lastCases Q (Fin.lastCases P params)
  let q := preservesAt f (fun i => i.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2))
  have hq : ∀ s, Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases s inputs) q ↔
      (ForcingNames.IsName P s → ∀ o, Mapped f params s o → ForcingNames.IsName Q o) := by
    intro s
    simpa only [q, inputs, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (preservesAt_semantics (Fin.lastCases s inputs) f (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last n).castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2)))
  have hAll := formula_induction hM q inputs (by
    intro s ih
    apply (hq s).mpr
    intro hn o ho
    apply ForcingNames.intro_name hM Q o
    intro z hz
    obtain ⟨tau, condition, v, c, he, hv, hc, hCode⟩ := (ForcingMapConditions.mem_mapping hM hf ho z).mp hz
    obtain ⟨hCondition, hTau⟩ := ForcingNames.child_condition hn he
    exact ⟨v, c, hCode, hInto condition c hCondition hc, (hq tau).mp (ih tau condition he) hTau v hv⟩)
  exact (hq sigma).mp (hAll sigma) hName output hm

def preservationSentence {n : Nat} (f : Formula (n+2)) : Source.Sentence :=
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  let P := (Fin.last n).castSucc.castSucc
  let Q := (Fin.last (n+1)).castSucc
  ((ForcingMapConditions.function f rho).imp ((mapsInto f rho P Q).imp
    (preservesAt f rho P Q (Fin.last (n+2))))).close

theorem preservation_models {n : Nat} (f : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (preservationSentence f)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hf hInto
  apply (preservesAt_semantics v f _ _ _ _).mpr
  intro hn output hm
  exact name_preservation hM ((ForcingMapConditions.function_semantics v f _).mp hf) _ _
    ((mapsInto_semantics v f _ _ _).mp hInto) hn hm

theorem preservation_kernel_certificate {n : Nat} (f : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (preservationSentence f)) :=
  ModelTransfer.derives (fun _ hM => preservation_models f hM)

/-- Object counterpart of the function extensionality used by Name's action laws. -/
def equivalentMaps {n m : Nat} (f g : Formula (n+2)) (rho : Fin n → Fin m) : Formula m :=
  .all (.all ((ReplacementPredicates.rel f (paramsUp (paramsUp rho))
    (Fin.last m).castSucc (Fin.last (m+1))).iff
      (ReplacementPredicates.rel g (paramsUp (paramsUp rho)) (Fin.last m).castSucc (Fin.last (m+1)))))

theorem equivalentMaps_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (f g : Formula (n+2)) (rho : Fin n → Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (equivalentMaps f g rho) ↔
      ∀ x y, MapRel f (fun i => v (rho i)) x y ↔ MapRel g (fun i => v (rho i)) x y := by
  simp only [equivalentMaps, Source.Formula.iff, Formula.Realize, ForcingMapConditions.rel_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩))

theorem mapping_congr {n : Nat} {f g : Formula (n+2)} {params : Fin n → M.Carrier .set}
    (he : ∀ x y, MapRel f params x y ↔ MapRel g params x y) (sigma output : M.Carrier .set) :
    Mapped f params sigma output ↔ Mapped g params sigma output := by
  have transfer : ∀ {a b : Formula (n+2)}, (∀ x y, MapRel a params x y ↔ MapRel b params x y) →
      Mapped a params sigma output → Mapped b params sigma output := by
    intro a b hab hm
    obtain ⟨graph, hGood, hEdge⟩ := hm
    refine ⟨graph, ?_, hEdge⟩
    intro s o hs
    obtain ⟨hc, hp⟩ := hGood s o hs
    refine ⟨hc, ?_⟩
    apply (ForcingMapConditions.operator_semantics b params s graph o).mpr
    have hEq := (ForcingMapConditions.operator_semantics a params s graph o).mp hp
    intro z
    constructor
    · intro hz
      obtain ⟨tau, condition, v, c, ht, hv, hr, hCode⟩ := (hEq z).mp hz
      exact ⟨tau, condition, v, c, ht, hv, (hab condition c).mp hr, hCode⟩
    · rintro ⟨tau, condition, v, c, ht, hv, hr, hCode⟩
      exact (hEq z).mpr ⟨tau, condition, v, c, ht, hv, (hab condition c).mpr hr, hCode⟩
  exact ⟨transfer he, transfer (fun x y => (he x y).symm)⟩

def congruenceSentence {n : Nat} (f g : Formula (n+2)) : Source.Sentence :=
  let rho : Fin n → Fin (n+2) := fun i => i.castSucc.castSucc
  ((equivalentMaps f g rho).imp ((mapping f rho (Fin.last n).castSucc (Fin.last (n+1))).iff
    (mapping g rho (Fin.last n).castSucc (Fin.last (n+1))))).close

theorem congruence_models {n : Nat} (f g : Formula (n+2)) :
    (Translation.sentence (congruenceSentence f g)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  have he := mapping_congr ((equivalentMaps_semantics v f g _).mp h)
    (v (Fin.last n).castSucc) (v (Fin.last (n+1)))
  have hf := ForcingMapConditions.mapping_semantics v f
    (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))
  have hg := ForcingMapConditions.mapping_semantics v g
    (fun i => i.castSucc.castSucc) (Fin.last n).castSucc (Fin.last (n+1))
  exact ⟨fun hm => hg.mpr (he.mp (hf.mp hm)), fun hm => hf.mpr (he.mpr (hg.mp hm))⟩

theorem congruence_kernel_certificate {n : Nat} (f g : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (congruenceSentence f g)) :=
  ModelTransfer.derives (fun _ _ => congruence_models f g)

end PPAC.Migration.ForcingMapLaws
