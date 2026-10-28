/- Pinned EquivariantMixing.MixEntries/mixTest/equivariantMix.
The family, activation graph and every literal child are internal sets.
Reuse the original collected-name constructor; no rank cutoff or choice of
a common strengthening is made. The flattened child index has exactly the
same raw entries as the source dependent sum of family edges. -/
import PPAC.Migration.ForcingCollectedName
import PPAC.Migration.ForcingAtomicLaws

namespace PPAC.Migration.ForcingMixName
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ReplacementPredicates (paramsUp rel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Children (J f child : M.Carrier .set) : Prop :=
  ∃ i sigma c, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J ∧
    PureKuratowski.PairMember M i sigma f ∧ PureKuratowski.PairMember M child c sigma

def children {m : Nat} (J f child : Fin m) : Formula m :=
  let up : Fin m → Fin (m+3) := fun i => i.castSucc.castSucc.castSucc
  let i := (Fin.last m).castSucc.castSucc
  let sigma := (Fin.last (m+1)).castSucc
  let c := Fin.last (m+2)
  .ex (.ex (.ex ((Formula.mem i (up J)).conj
    ((Source.SetLanguage.edge (up f) i sigma).conj (Source.SetLanguage.edge sigma (up child) c)))))

theorem children_semantics {m : Nat} (v : Fin m → M.Carrier .set) (J f child : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (children J f child) ↔
      Children (v J) (v f) (v child) := by
  simp only [children,Children,Formula.Realize,KuratowskiZF.source_edge,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def ChildCarrier (J f C : M.Carrier .set) : Prop := ∀ x,
  (Definitional.Project.FirstOrderSemantics.reduct M).mem x C ↔ Children J f x

theorem exists_children (hM : FirstOrder.Theory.Models M nativeZF) (J f : M.Carrier .set) :
    ∃ C, ChildCarrier J f C := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨b,hb⟩ := ForcingMapConditions.coordinate_bound hM f
  obtain ⟨U,hU⟩ := SetTheory.KP.exists_union (SetTheory.ZF.modelsKP hZF) b
  obtain ⟨c,hc⟩ := ForcingMapConditions.coordinate_bound hM U
  have bound x (hx : Children J f x) : (Definitional.Project.FirstOrderSemantics.reduct M).mem x c := by
    obtain ⟨i,sigma,q,_,hi,hxq⟩ := hx
    have he : PureKuratowski.PairMember M x q U := by
      obtain ⟨z,hz,hzs⟩ := hxq
      exact ⟨z,hz,(hU z).mpr ⟨sigma,(hb i sigma hi).2,hzs⟩⟩
    exact (hc x q he).1
  let query := children (0 : Fin 3) 1 2
  let env := Source.SetLanguage.args2 J f
  have hSep := (GodelDefOutput.separation_semantics
    (Definitional.Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨C,hC⟩ := hSep env c
  have he x : Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases x env) query ↔ Children J f x :=
    children_semantics (M := M) (Fin.lastCases x env) 0 1 2
  exact ⟨C,fun x => ⟨fun hx => (he x).mp ((hC x).mp hx).2,
    fun hx => (hC x).mpr ⟨bound x hx,(he x).mpr hx⟩⟩⟩

def EdgeEntry {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P J f a child p : M.Carrier .set) : Prop :=
  (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧
    ∃ i sigma t c, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J ∧
      PureKuratowski.PairMember M i sigma f ∧ PureKuratowski.PairMember M i t a ∧
      PureKuratowski.PairMember M child c sigma ∧ MapRel R env p t ∧
      Forces false R env P child sigma p

def edgeEntry {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m)
    (P J f a child p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let i := (Fin.last m).castSucc.castSucc.castSucc
  let sigma := (Fin.last (m+1)).castSucc.castSucc
  let t := (Fin.last (m+2)).castSucc
  let c := Fin.last (m+3)
  (Formula.mem p P).conj (.ex (.ex (.ex (.ex ((Formula.mem i (up J)).conj
    ((Source.SetLanguage.edge (up f) i sigma).conj ((Source.SetLanguage.edge (up a) i t).conj
      ((Source.SetLanguage.edge sigma (up child) c).conj
        ((rel R (fun j => up (rho j)) (up p) t).conj
          (ForcingAtomicRelations.forces false R (fun j => up (rho j)) (up P) (up child) sigma (up p)))))))))))

theorem edgeEntry_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a child p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v
      (edgeEntry R rho P J f a child p) ↔
        EdgeEntry R (fun j => v (rho j)) (v P) (v J) (v f) (v a) (v child) (v p) := by
  simp only [edgeEntry,EdgeEntry,Formula.Realize,KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),ForcingAtomicRelations.forces_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Entry {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P J f a z : M.Carrier .set) : Prop :=
  ∃ child p, PureKuratowski.Code M z child p ∧ EdgeEntry R env P J f a child p

def entry {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a z : Fin m) : Formula m :=
  .ex (.ex ((PairSyntax.ordered z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (edgeEntry R (paramsUp (paramsUp rho)) P.castSucc.castSucc J.castSucc.castSucc
      f.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem entry_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a z : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (entry R rho P J f a z) ↔
      Entry R (fun j => v (rho j)) (v P) (v J) (v f) (v a) (v z) := by
  simp only [entry,Entry,Formula.Realize,KuratowskiZF.source_code,edgeEntry_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Mix {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P J f a name : M.Carrier .set) : Prop :=
  ∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z name ↔ Entry R env P J f a z

def mix {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a name : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) name.castSucc).iff
    (entry R (paramsUp rho) P.castSucc J.castSucc f.castSucc a.castSucc (Fin.last m)))

theorem mix_semantics {n m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (n+2)) (rho : Fin n → Fin m) (P J f a name : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (mix R rho P J f a name) ↔
      Mix R (fun j => v (rho j)) (v P) (v J) (v f) (v a) (v name) := by
  simp only [mix,Mix,Source.Formula.iff,Formula.Realize,entry_semantics (M := M),
    paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)

def inputs {n : Nat} (env : Fin n → M.Carrier .set) (P J f a : M.Carrier .set) :
    Fin (n+4) → M.Carrier .set :=
  Fin.lastCases a (Fin.lastCases f (Fin.lastCases J (Fin.lastCases P env)))

def test {n : Nat} (R : Formula (n+2)) : Formula ((n+4)+2) :=
  edgeEntry R (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc
    (Fin.last (n+1)).castSucc.castSucc.castSucc.castSucc
    (Fin.last (n+2)).castSucc.castSucc.castSucc
    (Fin.last (n+3)).castSucc.castSucc (Fin.last (n+4)).castSucc (Fin.last (n+5))

theorem test_semantics {n : Nat} (R : Formula (n+2)) (env : Fin n → M.Carrier .set)
    (P J f a child p : M.Carrier .set) :
    MapRel (test R) (inputs env P J f a) child p ↔ EdgeEntry R env P J f a child p := by
  unfold MapRel test
  simpa only [inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
    edgeEntry_semantics (M := M) (Fin.lastCases p (Fin.lastCases child (inputs env P J f a))) R
      (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc.castSucc.castSucc.castSucc
      (Fin.last (n+1)).castSucc.castSucc.castSucc.castSucc
      (Fin.last (n+2)).castSucc.castSucc.castSucc (Fin.last (n+3)).castSucc.castSucc
      (Fin.last (n+4)).castSucc (Fin.last (n+5))

theorem collected_iff {n : Nat} {R : Formula (n+2)} {env : Fin n → M.Carrier .set}
    {P J f a C idC name : M.Carrier .set} (hC : ChildCarrier J f C)
    (hid : ForcingConditionGraphs.IdentityGraph C idC) :
    ForcingCollectedName.Collected (test R) (inputs env P J f a) C idC P name ↔ Mix R env P J f a name := by
  have he child p : ForcingCollectedName.Admissible (test R) (inputs env P J f a) C idC P child p ↔
      EdgeEntry R env P J f a child p := by
    constructor
    · rintro ⟨_,x,_,hx,ht⟩
      have hx' := ((hid x child).mp hx).2
      subst x
      exact (test_semantics R env P J f a child p).mp ht
    · intro ht
      obtain ⟨i,sigma,t,c,hi,hf,_,hc,_,_⟩ := ht.2
      have hchild := (hC child).mpr ⟨i,sigma,c,hi,hf,hc⟩
      exact ⟨ht.1,child,hchild,(hid child child).mpr ⟨hchild,rfl⟩,
        (test_semantics R env P J f a child p).mpr ht⟩
  constructor
  · intro h z
    constructor
    · intro hz
      obtain ⟨child,p,ha,hz⟩ := (h z).mp hz
      exact ⟨child,p,hz,(he child p).mp ha⟩
    · rintro ⟨child,p,hz,ha⟩
      exact (h z).mpr ⟨child,p,(he child p).mpr ha,hz⟩
  · intro h z
    constructor
    · intro hz
      obtain ⟨child,p,hz,ha⟩ := (h z).mp hz
      exact ⟨child,p,(he child p).mpr ha,hz⟩
    · rintro ⟨child,p,ha,hz⟩
      exact (h z).mpr ⟨child,p,hz,(he child p).mp ha⟩

theorem exists_mix (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (env : Fin n → M.Carrier .set) (P J f a : M.Carrier .set) :
    ∃ name, Mix R env P J f a name := by
  obtain ⟨C,hC⟩ := exists_children hM J f
  obtain ⟨idC,_,hid⟩ := ForcingConditionGraphs.exists_identity hM C
  obtain ⟨name,hn⟩ := ForcingCollectedName.exists_collected hM (test R) (inputs env P J f a) C idC P
  exact ⟨name,(collected_iff hC hid).mp hn⟩

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P J f a x y : M.Carrier .set}
    (hx : Mix R env P J f a x) (hy : Mix R env P J f a y) : x = y :=
  (ModelTransfer.extensionality hM).eq_of_same_members x y (fun z => (hx z).trans (hy z).symm)

theorem edge_mix (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P J f a name : M.Carrier .set}
    (hn : Mix R env P J f a name) (child p : M.Carrier .set) :
    PureKuratowski.PairMember M child p name ↔ EdgeEntry R env P J f a child p := by
  constructor
  · rintro ⟨z,hz,hzn⟩
    obtain ⟨x,q,hz',he⟩ := (hn z).mp hzn
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
    exact he
  · intro he
    obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM child p
    exact ⟨z,hz,(hn z).mpr ⟨child,p,hz,he⟩⟩

theorem isName (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {env : Fin n → M.Carrier .set} {P J f a name : M.Carrier .set}
    (hn : Mix R env P J f a name)
    (hf : ∀ i sigma, (Definitional.Project.FirstOrderSemantics.reduct M).mem i J →
      PureKuratowski.PairMember M i sigma f → ForcingNames.IsName P sigma) : ForcingNames.IsName P name := by
  apply ForcingNames.intro_name hM P name
  intro z hz
  obtain ⟨child,p,hz,hp,i,sigma,t,c,hi,hf',_,hc,_,_⟩ := (hn z).mp hz
  exact ⟨child,p,hz,hp,(ForcingNames.child_condition (hf i sigma hi hf') hc).2⟩

def existenceSentence {n : Nat} (R : Formula (n+2)) (P J f a : Fin n) : Source.Sentence :=
  (Formula.ex (mix R (paramsUp id) P.castSucc J.castSucc f.castSucc a.castSucc (Fin.last n))).close

theorem existence_models {n : Nat} (R : Formula (n+2)) (P J f a : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence R P J f a)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env
  obtain ⟨name,hn⟩ := exists_mix hM R env (env P) (env J) (env f) (env a)
  refine ⟨name,?_⟩
  apply (mix_semantics (M := M) (Fin.lastCases name env) R (paramsUp id)
    P.castSucc J.castSucc f.castSucc a.castSucc (Fin.last n)).mpr
  simpa only [paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] using hn

theorem existence_kernel_certificate {n : Nat} (R : Formula (n+2)) (P J f a : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence R P J f a)) :=
  ModelTransfer.derives (fun _ hM => existence_models R P J f a hM)

end PPAC.Migration.ForcingMixName
