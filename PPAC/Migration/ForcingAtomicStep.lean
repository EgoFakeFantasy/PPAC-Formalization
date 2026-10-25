/- Object adaptation of pinned AtomicForcing.lean: relations (lines 49-62).
The two truth sets are separated from the internal condition set P. The order
is a formula with arbitrary parameters. A row stores ((sigma,tau),(mem,eq)).
Only recursive queries to the three source predecessors occur. This constructs
the concrete step, not a solution of its recursive equations. No forcing law,
external well-foundedness, choice function, or rank bound is assumed. -/
import PPAC.Migration.ForcingMapLaws

namespace PPAC.Migration.ForcingAtomicStep
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def row {m : Nat} (g x y a b : Fin m) : Formula m :=
  .ex (.ex ((PairSyntax.ordered (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc).conj
    ((PairSyntax.ordered (Fin.last (m+1)) a.castSucc.castSucc b.castSucc.castSucc).conj
      (Source.SetLanguage.edge g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def Row (g x y a b : M.Carrier .set) : Prop :=
  ∃ key value, PureKuratowski.Code M key x y ∧ PureKuratowski.Code M value a b ∧
    PureKuratowski.PairMember M key value g

theorem row_semantics {m : Nat} (v : Fin m → M.Carrier .set) (g x y a b : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (row g x y a b) ↔
      Row (v g) (v x) (v y) (v a) (v b) := by
  simp only [row, Formula.Realize, KuratowskiZF.source_code, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, Row]
  rfl

def query {m : Nat} (equality : Bool) (g x y p : Fin m) : Formula m :=
  .ex (.ex ((row g.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))).conj
      (.mem p.castSucc.castSucc (if equality then Fin.last (m+1) else (Fin.last m).castSucc))))

def Query (equality : Bool) (g x y p : M.Carrier .set) : Prop :=
  ∃ a b, Row g x y a b ∧ (Definitional.Project.FirstOrderSemantics.reduct M).mem p (if equality then b else a)

theorem query_semantics {m : Nat} (v : Fin m → M.Carrier .set) (equality : Bool) (g x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (query equality g x y p) ↔
      Query equality (v g) (v x) (v y) (v p) := by
  cases equality <;> simp only [query, Query, Formula.Realize, row_semantics (M := M),
    Bool.false_eq_true, if_false, if_true, Fin.lastCases_last, Fin.lastCases_castSucc] <;> rfl

def memBody {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P g x y p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let q := (Fin.last m).castSucc.castSucc.castSucc
  let s := (Fin.last (m+1)).castSucc.castSucc
  let nu := (Fin.last (m+2)).castSucc
  let r := Fin.last (m+3)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (paramsUp rho) (Fin.last m) p.castSucc).imp
      (.ex (.ex (.ex ((Formula.mem s (up P)).conj
        ((ReplacementPredicates.rel R (fun i => up (rho i)) s q).conj
          ((Formula.mem r (up P)).conj ((Source.SetLanguage.edge (up y) nu r).conj
            ((ReplacementPredicates.rel R (fun i => up (rho i)) s r).conj
              (query true (up g) (up x) nu s)))))))))))

def MemBody {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P g x y p : M.Carrier .set) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
    ∃ s nu r, (Definitional.Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R params s q ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ PureKuratowski.PairMember M nu r y ∧
        MapRel R params s r ∧ Query true g x nu s

def eqHalf {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P g x y p : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
    ((Source.SetLanguage.edge x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.all ((Formula.mem (Fin.last (m+2)) P.castSucc.castSucc.castSucc).imp
        ((ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
          (Fin.last (m+2)) p.castSucc.castSucc.castSucc).imp
          ((ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
            (Fin.last (m+2)) (Fin.last (m+1)).castSucc).imp
            (query false g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
              y.castSucc.castSucc.castSucc (Fin.last (m+2))))))))))

def EqHalf {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P g x y p : M.Carrier .set) : Prop :=
  ∀ nu r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → PureKuratowski.PairMember M nu r x →
    ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
      MapRel R params q r → Query false g nu y q

def eqBody {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P g x y p : Fin m) : Formula m :=
  (eqHalf R rho P g x y p).conj (eqHalf R rho P g y x p)

def EqBody {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P g x y p : M.Carrier .set) : Prop := EqHalf R params P g x y p ∧ EqHalf R params P g y x p

theorem memBody_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P g x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (memBody R rho P g x y p) ↔
      MemBody R (fun i => v (rho i)) (v P) (v g) (v x) (v y) (v p) := by
  simp only [memBody, MemBody, Formula.Realize, KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M), query_semantics (M := M), paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem eqHalf_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P g x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (eqHalf R rho P g x y p) ↔
      EqHalf R (fun i => v (rho i)) (v P) (v g) (v x) (v y) (v p) := by
  simp only [eqHalf, EqHalf, Formula.Realize, KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M), query_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem eqBody_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P g x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (eqBody R rho P g x y p) ↔
      EqBody R (fun i => v (rho i)) (v P) (v g) (v x) (v y) (v p) := by
  simp only [eqBody, EqBody, Formula.Realize, eqHalf_semantics (M := M)]

def equation {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P g x y output : Fin m) : Formula m :=
  .ex (.ex ((PairSyntax.ordered output.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    ((Formula.all ((Formula.mem (Fin.last (m+2)) (Fin.last m).castSucc.castSucc).iff
      ((Formula.mem (Fin.last (m+2)) P.castSucc.castSucc.castSucc).conj
        (memBody R (fun i => (rho i).castSucc.castSucc.castSucc)
          P.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc
          y.castSucc.castSucc.castSucc (Fin.last (m+2)))))).conj
      (.all ((Formula.mem (Fin.last (m+2)) (Fin.last (m+1)).castSucc).iff
        ((Formula.mem (Fin.last (m+2)) P.castSucc.castSucc.castSucc).conj
          (eqBody R (fun i => (rho i).castSucc.castSucc.castSucc)
            P.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc
            y.castSucc.castSucc.castSucc (Fin.last (m+2)))))))))

def Equation {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P g x y output : M.Carrier .set) : Prop :=
  ∃ a b, PureKuratowski.Code M output a b ∧
    (∀ p, (Definitional.Project.FirstOrderSemantics.reduct M).mem p a ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧ MemBody R params P g x y p) ∧
    (∀ p, (Definitional.Project.FirstOrderSemantics.reduct M).mem p b ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧ EqBody R params P g x y p)

theorem equation_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P g x y output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (equation R rho P g x y output) ↔
      Equation R (fun i => v (rho i)) (v P) (v g) (v x) (v y) (v output) := by
  simp only [equation, Equation, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_code,
    memBody_semantics (M := M), eqBody_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  constructor
  · rintro ⟨a,b,hc,ha,hb⟩
    exact ⟨a,b,hc,(fun p => ⟨(ha p).1,(ha p).2⟩),(fun p => ⟨(hb p).1,(hb p).2⟩)⟩
  · rintro ⟨a,b,hc,ha,hb⟩
    exact ⟨a,b,hc,(fun p => ⟨(ha p).mp,(ha p).mpr⟩),(fun p => ⟨(hb p).mp,(hb p).mpr⟩)⟩

theorem equation_exists (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P g x y : M.Carrier .set) :
    ∃ output, Equation R params P g x y output := by
  let E := (Definitional.Project.FirstOrderSemantics.reduct M).mem
  let inputs : Fin (n+4) → M.Carrier .set := Fin.lastCases y (Fin.lastCases x (Fin.lastCases g (Fin.lastCases P params)))
  let rho : Fin n → Fin (n+5) := fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc
  let pp := (Fin.last n).castSucc.castSucc.castSucc.castSucc
  let gg := (Fin.last (n+1)).castSucc.castSucc.castSucc
  let xx := (Fin.last (n+2)).castSucc.castSucc
  let yy := (Fin.last (n+3)).castSucc
  let mm := memBody R rho pp gg xx yy (Fin.last (n+4))
  let ee := eqBody R rho pp gg xx yy (Fin.last (n+4))
  have hm := (GodelDefOutput.separation_semantics E mm).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation mm).semantically_entails M hM))
  have he := (GodelDefOutput.separation_semantics E ee).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation ee).semantically_entails M hM))
  obtain ⟨a, ha⟩ := hm inputs P
  obtain ⟨b, hb⟩ := he inputs P
  obtain ⟨output, ho⟩ := KuratowskiZF.exists_code hM a b
  refine ⟨output, a, b, ho, ?_, ?_⟩
  · intro p
    apply (ha p).trans
    apply and_congr Iff.rfl
    simpa only [mm, E, inputs, rho, pp, gg, xx, yy, Fin.lastCases_last, Fin.lastCases_castSucc] using
      memBody_semantics (M := M) (Fin.lastCases p inputs) R rho pp gg xx yy (Fin.last (n+4))
  · intro p
    apply (hb p).trans
    apply and_congr Iff.rfl
    simpa only [ee, E, inputs, rho, pp, gg, xx, yy, Fin.lastCases_last, Fin.lastCases_castSucc] using
      eqBody_semantics (M := M) (Fin.lastCases p inputs) R rho pp gg xx yy (Fin.last (n+4))

theorem equation_unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P g x y a b : M.Carrier .set}
    (ha : Equation R params P g x y a) (hb : Equation R params P g x y b) : a = b := by
  obtain ⟨ma, ea, hca, hma, hea⟩ := ha
  obtain ⟨mb, eb, hcb, hmb, heb⟩ := hb
  have hm : ma = mb := (ModelTransfer.extensionality hM).eq_of_same_members ma mb
    (fun p => (hma p).trans (hmb p).symm)
  have he : ea = eb := (ModelTransfer.extensionality hM).eq_of_same_members ea eb
    (fun p => (hea p).trans (heb p).symm)
  subst mb
  subst eb
  exact KuratowskiZF.code_unique hM hca hcb

theorem query_congr {g h x y p : M.Carrier .set} (equality : Bool)
    (ha : ∀ a b, Row g x y a b ↔ Row h x y a b) : Query equality g x y p ↔ Query equality h x y p := by
  constructor
  · rintro ⟨a,b,hr,hp⟩
    exact ⟨a,b,(ha a b).mp hr,hp⟩
  · rintro ⟨a,b,hr,hp⟩
    exact ⟨a,b,(ha a b).mpr hr,hp⟩

/-- Only the right predecessor is queried by the original membership clause. -/
theorem memBody_congr {n : Nat} {R : Formula (n+2)} {params : Fin n → M.Carrier .set}
    {P g h x y p : M.Carrier .set}
    (ha : ∀ nu r, PureKuratowski.PairMember M nu r y → ∀ a b, Row g x nu a b ↔ Row h x nu a b) :
    MemBody R params P g x y p ↔ MemBody R params P h x y p := by
  constructor
  · intro hg q hq hqp
    obtain ⟨s,nu,r,hs,hsq,hr,hy,hsr,ht⟩ := hg q hq hqp
    exact ⟨s,nu,r,hs,hsq,hr,hy,hsr,(query_congr true (ha nu r hy)).mp ht⟩
  · intro hh q hq hqp
    obtain ⟨s,nu,r,hs,hsq,hr,hy,hsr,ht⟩ := hh q hq hqp
    exact ⟨s,nu,r,hs,hsq,hr,hy,hsr,(query_congr true (ha nu r hy)).mpr ht⟩

theorem eqHalf_congr {n : Nat} {R : Formula (n+2)} {params : Fin n → M.Carrier .set}
    {P g h x y p : M.Carrier .set}
    (ha : ∀ nu r, PureKuratowski.PairMember M nu r x → ∀ a b, Row g nu y a b ↔ Row h nu y a b) :
    EqHalf R params P g x y p ↔ EqHalf R params P h x y p := by
  constructor
  · intro hg nu r hr hx q hq hqp hqr
    exact (query_congr false (ha nu r hx)).mp (hg nu r hr hx q hq hqp hqr)
  · intro hh nu r hr hx q hq hqp hqr
    exact (query_congr false (ha nu r hx)).mpr (hh nu r hr hx q hq hqp hqr)

/-- Exact three source recursive dependencies; no global graph agreement. -/
theorem equation_congr {n : Nat} {R : Formula (n+2)} {params : Fin n → M.Carrier .set}
    {P g h x y output : M.Carrier .set}
    (hl : ∀ nu r, PureKuratowski.PairMember M nu r x → ∀ a b, Row g nu y a b ↔ Row h nu y a b)
    (hr : ∀ nu r, PureKuratowski.PairMember M nu r y → ∀ a b, Row g x nu a b ↔ Row h x nu a b)
    (hs : ∀ nu r, PureKuratowski.PairMember M nu r y → ∀ a b, Row g nu x a b ↔ Row h nu x a b) :
    Equation R params P g x y output ↔ Equation R params P h x y output := by
  have hm : ∀ p, MemBody R params P g x y p ↔ MemBody R params P h x y p := fun _ => memBody_congr hr
  have he : ∀ p, EqBody R params P g x y p ↔ EqBody R params P h x y p :=
    fun _ => and_congr (eqHalf_congr hl) (eqHalf_congr hs)
  constructor
  · rintro ⟨a,b,hc,ha,hb⟩
    exact ⟨a,b,hc,(fun p => (ha p).trans (and_congr Iff.rfl (hm p))),
      (fun p => (hb p).trans (and_congr Iff.rfl (he p)))⟩
  · rintro ⟨a,b,hc,ha,hb⟩
    exact ⟨a,b,hc,(fun p => (ha p).trans (and_congr Iff.rfl (hm p).symm)),
      (fun p => (hb p).trans (and_congr Iff.rfl (he p).symm))⟩

def existenceSentence {n : Nat} (R : Formula (n+2)) (P g x y : Fin n) : Source.Sentence :=
  (Formula.ex (equation R Fin.castSucc P.castSucc g.castSucc x.castSucc y.castSucc (Fin.last n))).close

def uniquenessSentence {n : Nat} (R : Formula (n+2)) (P g x y a b : Fin n) : Source.Sentence :=
  ((equation R id P g x y a).imp ((equation R id P g x y b).imp (.equal a b))).close

theorem existence_models {n : Nat} (R : Formula (n+2)) (P g x y : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (existenceSentence R P g x y)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨output, ho⟩ := equation_exists hM R v (v P) (v g) (v x) (v y)
  refine ⟨output, ?_⟩
  have he := equation_semantics (M := M) (Fin.lastCases output v) R Fin.castSucc
    P.castSucc g.castSucc x.castSucc y.castSucc (Fin.last n)
  simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at he
  exact he.mpr ho

theorem uniqueness_models {n : Nat} (R : Formula (n+2)) (P g x y a b : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence R P g x y a b)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v ha hb
  exact equation_unique hM ((equation_semantics (M := M) v R id P g x y a).mp ha)
    ((equation_semantics (M := M) v R id P g x y b).mp hb)

theorem existence_kernel_certificate {n : Nat} (R : Formula (n+2)) (P g x y : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (existenceSentence R P g x y)) :=
  ModelTransfer.derives (fun _ hM => existence_models R P g x y hM)

theorem uniqueness_kernel_certificate {n : Nat} (R : Formula (n+2)) (P g x y a b : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence R P g x y a b)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models R P g x y a b hM)

end PPAC.Migration.ForcingAtomicStep
