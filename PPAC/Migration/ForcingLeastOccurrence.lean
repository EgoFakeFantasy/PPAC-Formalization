/- Pinned OrderedSections.LeastOccurrence at the INTERNAL ordinal indices
used by wellordered images and SliceData.O. Reuse existing original-kernel
ordinal minima. No host well-founded relation or standardness assumption. -/
import PPAC.Migration.ForcingSubsetImage
import PPAC.Migration.ForcingOrdinalDecision

namespace PPAC.Migration.ForcingLeastOccurrence
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingClassEvaluation (Predicate)
open ForcingRelationGraphForcing (Holds)
open ForcingRawRank (Ordinal)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Source subtype membership is explicit; smaller indices use the SAME
internal ordinal membership relation. Names/conditions remain unrestricted. -/
def At {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (env : Fin k → M.Carrier .set)
    (P O p x i : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i O ∧ Holds Q env p x i ∧
    ∀ j, (Project.FirstOrderSemantics.reduct M).mem j O →
      (Project.FirstOrderSemantics.reduct M).mem j i → ∀ q,
        (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p → ¬ Holds Q env q x j

def atFormula {k m : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (base : Fin k → Fin m)
    (P O p x i : Fin m) : Formula m :=
  (Formula.mem i O).conj ((ForcingRelationGraphSupport.relation Q base p x i).conj
    (.all ((Formula.mem (Fin.last m) O.castSucc).imp
      ((Formula.mem (Fin.last m) i.castSucc).imp (.all
        ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
          ((ReplacementPredicates.rel L (fun j => (base j).castSucc.castSucc)
            (Fin.last (m+1)) p.castSucc.castSucc).imp
              (ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc)
                (Fin.last (m+1)) x.castSucc.castSucc (Fin.last m).castSucc).neg)))))))

theorem at_semantics {k m : Nat} (v : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (Q : Formula (k+3)) (base : Fin k → Fin m) (P O p x i : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (atFormula L Q base P O p x i) ↔
      At L Q (fun j => v (base j)) (v P) (v O) (v p) (v x) (v i) := by
  simp only [atFormula,At,Formula.Realize,Source.Formula.neg,Formula.Realize,
    ForcingMapConditions.rel_semantics (M := M),ForcingRelationGraphSupport.relation_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Compatibility before minimization is itself an object formula. -/
def Possible {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (env : Fin k → M.Carrier .set)
    (P O q x i : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i O ∧ ∃ r,
    (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧ Holds Q env r x i

def possible {k m : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (base : Fin k → Fin m)
    (P O q x i : Fin m) : Formula m :=
  (Formula.mem i O).conj (.ex ((Formula.mem (Fin.last m) P.castSucc).conj
    ((ReplacementPredicates.rel L (fun j => (base j).castSucc) (Fin.last m) q.castSucc).conj
      (ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc) (Fin.last m) x.castSucc i.castSucc))))

theorem possible_semantics {k m : Nat} (v : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (Q : Formula (k+3)) (base : Fin k → Fin m) (P O q x i : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (possible L Q base P O q x i) ↔
      Possible L Q (fun j => v (base j)) (v P) (v O) (v q) (v x) (v i) := by
  simp only [possible,Possible,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingRelationGraphSupport.relation_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- Instantiate the EXISTING ObjectOrdinalLeast schema at compatibility.
All witnesses/minima are internal sets, including in nonstandard models. -/
theorem least_possible (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (L : Formula (k+2)) (Q : Formula (k+3)) (env : Fin k → M.Carrier .set)
    (P O q x : M.Carrier .set) (hO : Ordinal O)
    (hExists : ∃ i, Possible L Q env P O q x i) :
    ∃ i, Possible L Q env P O q x i ∧
      ∀ j, Possible L Q env P O q x j → i = j ∨ (Project.FirstOrderSemantics.reduct M).mem i j := by
  let inputs : Fin (k+4) → M.Carrier .set := Fin.lastCases x (Fin.lastCases q (Fin.lastCases O (Fin.lastCases P env)))
  let matrix := possible L Q (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc)
    (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
    (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have hMatrix (i : M.Carrier .set) : Predicate matrix inputs i ↔ Possible L Q env P O q x i := by
    unfold Predicate
    simpa only [matrix,inputs,Fin.lastCases_last,Fin.lastCases_castSucc] using
      possible_semantics (M := M) (Fin.lastCases i inputs) L Q
        (fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc)
        (Fin.last k).castSucc.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc.castSucc.castSucc
        (Fin.last (k+2)).castSucc.castSucc (Fin.last (k+3)).castSucc (Fin.last (k+4))
  have h := ForcingRawRank.closed_truth hM
    ((OrdinalLeastSyntax.has matrix id).imp (OrdinalLeastSyntax.leastExists matrix id))
    (ObjectOrdinalLeast.native_existence matrix) inputs
  simp only [OrdinalLeastSyntax.has,OrdinalLeastSyntax.leastExists,OrdinalLeastSyntax.least,
    OrdinalLeastSyntax.property,Formula.Realize,ForcingRawRank.ordinal_semantics (M := M),
    ForcingClassEvaluation.predicate_semantics (M := M),ReplacementPredicates.paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc,id_eq] at h
  obtain ⟨j,hj⟩ := hExists
  obtain ⟨i,⟨_hi,hmi⟩,hMin⟩ := h ⟨j,ForcingRawRank.ordinal_member hM hO hj.1,(hMatrix j).mpr hj⟩
  refine ⟨i,(hMatrix i).mp hmi,?_⟩
  intro j hj
  exact hMin j ⟨ForcingRawRank.ordinal_member hM hO hj.1,(hMatrix j).mpr hj⟩

/-- The same dense minimum argument as source, using its internal ordinal
index order and the completed original-kernel minimality schema. -/
theorem dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (L : Formula (k+2)) (Q : Formula (k+3)) (env : Fin k → M.Carrier .set)
    (P O p x : M.Carrier .set) (hO : Ordinal O)
    (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧
        ∃ i, (Project.FirstOrderSemantics.reduct M).mem i O ∧ Holds Q env r x i) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p →
      ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧ ∃ i, At L Q env P O r x i := by
  intro q hq hqp
  obtain ⟨r,hr,hrq,i,hi,hRi⟩ := h q hq hqp
  obtain ⟨i,⟨hi,r,hr,hrq,hRi⟩,hMin⟩ := least_possible hM L Q env P O q x hO ⟨i,hi,r,hr,hrq,hRi⟩
  refine ⟨r,hr,hrq,i,hi,hRi,?_⟩
  intro j hj hji s hs hsr hRj
  have hh := hMin j ⟨hj,s,hs,hpre.2 s r q hs hr hq hsr hrq,hRj⟩
  have hiOrd := ForcingRawRank.ordinal_member hM hO hi
  rcases hh with he | hij
  · cases he
    exact ForcingOrdinalDecision.ordinal_irrefl hM hiOrd hji
  · exact ForcingOrdinalDecision.ordinal_irrefl hM hiOrd
      (ForcingRawRank.ordinal_transitive hiOrd j hji i hij)

/-- Same-index uniqueness is literal internal set equality, not forced
name equality or an external ordinal comparison. -/
theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {Q : Formula (k+3)} {env : Fin k → M.Carrier .set}
    {P O p x i j : M.Carrier .set} (hO : Ordinal O)
    (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hi : At L Q env P O p x i) (hj : At L Q env P O p x j) : i = j := by
  rcases ForcingOrdinalDecision.ordinal_compare hM
    (ForcingRawRank.ordinal_member hM hO hi.1) (ForcingRawRank.ordinal_member hM hO hj.1) with he | hij | hji
  · exact he
  · exact (hj.2.2 i hi.1 hij p hp (hpre.1 p hp) hi.2.1).elim
  · exact (hi.2.2 j hj.1 hji p hp (hpre.1 p hp) hj.2.1).elim

/-- Source monotonicity; only the already supplied occurrence laws are used. -/
theorem mono {k : Nat} {L : Formula (k+2)} {Q : Formula (k+3)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {P O p q x i : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hMono : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p q,
      (Project.FirstOrderSemantics.reduct M).mem p P → (Project.FirstOrderSemantics.reduct M).mem q P →
      MapRel L env q p → ∀ x, Predicate H env x → Holds Q env p x i → Holds Q env q x i)
    (hx : Predicate H env x) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel L env q p)
    (hi : At L Q env P O p x i) : At L Q env P O q x i := by
  refine ⟨hi.1,hMono i hi.1 p q hp hq hqp x hx hi.2.1,?_⟩
  intro j hj hji r hr hrq
  exact hi.2.2 j hj hji r hr (hpre.2 r q p hr hq hp hrq hqp)

/-- Source congruence changes the name but leaves its INTERNAL ordinal index
literal. Occurrence congruence is exactly the source UnaryRelation input. -/
theorem congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {L : Formula (k+2)} {Q : Formula (k+3)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P O p x y i : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hCongr : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p,
      (Project.FirstOrderSemantics.reduct M).mem p P → ∀ x y, Predicate H env x → Predicate H env y →
      Forces true L env P x y p → (Holds Q env p x i ↔ Holds Q env p y i))
    (hx : Predicate H env x) (hy : Predicate H env y)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (he : Forces true L env P x y p) :
    At L Q env P O p x i ↔ At L Q env P O p y i := by
  have step {x y} (hx : Predicate H env x) (hy : Predicate H env y)
      (he : Forces true L env P x y p) (hi : At L Q env P O p x i) : At L Q env P O p y i := by
    refine ⟨hi.1,(hCongr i hi.1 p hp x y hx hy he).mp hi.2.1,?_⟩
    intro j hj hji q hq hqp hh
    exact hi.2.2 j hj hji q hq hqp ((hCongr j hj q hq x y hx hy
      (ForcingAtomicBasic.eq_mono hM hpre hq hqp he)).mpr hh)
  exact ⟨step hx hy he,step hy hx (ForcingAtomicBasic.eq_symm hM he)⟩

/-- Regularity of the source least-occurrence predicate. All dense witnesses
remain internal conditions, without selecting a family of representatives. -/
theorem regular {k : Nat} {L : Formula (k+2)} {Q : Formula (k+3)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {P O p x i : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn L env P)
    (hMono : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p q,
      (Project.FirstOrderSemantics.reduct M).mem p P → (Project.FirstOrderSemantics.reduct M).mem q P →
      MapRel L env q p → ∀ x, Predicate H env x → Holds Q env p x i → Holds Q env q x i)
    (hRegular : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i O → ∀ p,
      (Project.FirstOrderSemantics.reduct M).mem p P → ∀ x, Predicate H env x →
      (∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧ Holds Q env r x i) → Holds Q env p x i)
    (hx : Predicate H env x) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p → ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧ At L Q env P O r x i) : At L Q env P O p x i := by
  obtain ⟨_,_,_,hi⟩ := h p hp (hpre.1 p hp)
  refine ⟨hi.1,hRegular i hi.1 p hp x hx (fun q hq hqp => by
    obtain ⟨r,hr,hrq,hi⟩ := h q hq hqp
    exact ⟨r,hr,hrq,hi.2.1⟩),?_⟩
  intro j hj hji q hq hqp hh
  obtain ⟨r,hr,hrq,hi⟩ := h q hq hqp
  exact hi.2.2 j hj hji r hr (hpre.1 r hr) (hMono j hj q r hq hr hrq x hx hh)

/-- A Boolean selects the two sides of the SAME source dense implication;
it does not restrict the internal name, condition or ordinal quantifiers. -/
def Dense {k : Nat} (useLeast : Bool) (L : Formula (k+2)) (Q : Formula (k+3))
    (env : Fin k → M.Carrier .set) (P O p x : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel L env q p →
    ∃ r, (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel L env r q ∧
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i O ∧
        (if useLeast then At L Q env P O r x i else Holds Q env r x i)

def densely {k m : Nat} (useLeast : Bool) (L : Formula (k+2)) (Q : Formula (k+3))
    (base : Fin k → Fin m) (P O p x : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel L (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        ((ReplacementPredicates.rel L (fun j => (base j).castSucc.castSucc) (Fin.last (m+1)) (Fin.last m).castSucc).conj
          (.ex ((Formula.mem (Fin.last (m+2)) O.castSucc.castSucc.castSucc).conj
            (if useLeast then atFormula L Q (fun j => (base j).castSucc.castSucc.castSucc)
              P.castSucc.castSucc.castSucc O.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc
              x.castSucc.castSucc.castSucc (Fin.last (m+2))
             else ForcingRelationGraphSupport.relation Q (fun j => (base j).castSucc.castSucc.castSucc)
               (Fin.last (m+1)).castSucc x.castSucc.castSucc.castSucc (Fin.last (m+2))))))))))

theorem densely_semantics {k m : Nat} (useLeast : Bool) (v : Fin m → M.Carrier .set)
    (L : Formula (k+2)) (Q : Formula (k+3)) (base : Fin k → Fin m) (P O p x : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (densely useLeast L Q base P O p x) ↔
      Dense useLeast L Q (fun j => v (base j)) (v P) (v O) (v p) (v x) := by
  cases useLeast <;>
    simp only [densely,Dense,Bool.false_eq_true,if_false,if_true,Formula.Realize,
      ForcingMapConditions.rel_semantics (M := M),ForcingRelationGraphSupport.relation_semantics (M := M),
      at_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc] <;> rfl

/-- Both genuine source conclusions: dense least occurrences and literal
uniqueness of the index. Background preorder/ordinal guards are explicit. -/
def sentence {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (P O p x i j : Fin k) : Source.Sentence :=
  ((ForcingAtomicBasic.preorder L id P).imp ((OrdinalSyntax.ordinal O).imp
    ((Formula.mem p P).imp
      (((densely false L Q id P O p x).imp (densely true L Q id P O p x)).conj
        ((atFormula L Q id P O p x i).imp ((atFormula L Q id P O p x j).imp (.equal i j))))))).close

theorem models {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (P O p x i j : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence L Q P O p x i j)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hPre hO hp
  have hpre := (ForcingAtomicBasic.preorder_semantics (M := M) env L id P).mp hPre
  have hOrd := (ForcingRawRank.ordinal_semantics (M := M) env O).mp hO
  constructor
  · intro hDense
    have hd := (densely_semantics false env L Q id P O p x).mp hDense
    have ho := dense hM L Q env (env P) (env O) (env p) (env x) hOrd hpre hd
    apply (densely_semantics true env L Q id P O p x).mpr
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,hi⟩ := ho q hq hqp
    exact ⟨r,hr,hrq,i,hi.1,hi⟩
  · intro hi hj
    exact unique hM hOrd hpre hp ((at_semantics env L Q id P O p x i).mp hi)
      ((at_semantics env L Q id P O p x j).mp hj)

/-- Original YesMetaZFC proof kernel; the existing minimum schema discharges
all ordinal well-foundedness internally. No L or Choice premise. -/
theorem kernel_certificate {k : Nat} (L : Formula (k+2)) (Q : Formula (k+3)) (P O p x i j : Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence L Q P O p x i j)) :=
  ModelTransfer.derives (fun _ hM => models L Q P O p x i j hM)

end PPAC.Migration.ForcingLeastOccurrence
