/- Fixed OrbitAssignments.Assigned:401-405 and orbitAssignment_index:450-455.
The same sixteen actual internal functions fix the per-orbit auxiliary inputs.
Assigned quantifies the whole orbit quotient and actual fields, then uses the
existing OrbitAssignment formula. No host choice function defines the assignment.
Existence of the whole auxiliary family is a separate, still required assembly. -/
import PPAC.Migration.ForcingOrbitIndex
import PPAC.Migration.ForcingOrbitRepresentativeDensity

namespace PPAC.Migration.ForcingAssigned
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingOrbitAssignment (OrbitAssignment orbitAssignment)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Fields {k : Nat} (env : Fin k → M.Carrier .set) (families : Fin 16 → Fin k)
    (a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M a root (env (families 0)) ∧
    PureKuratowski.PairMember M a chain (env (families 1)) ∧
    PureKuratowski.PairMember M a codes (env (families 2)) ∧
    PureKuratowski.PairMember M a order (env (families 3)) ∧
    PureKuratowski.PairMember M a ranks (env (families 4)) ∧
    PureKuratowski.PairMember M a selection (env (families 5)) ∧
    PureKuratowski.PairMember M a rankBound (env (families 6)) ∧
    PureKuratowski.PairMember M a labelSet (env (families 7)) ∧
    PureKuratowski.PairMember M a tab (env (families 8)) ∧
    PureKuratowski.PairMember M a r (env (families 9)) ∧
    PureKuratowski.PairMember M a germGroup (env (families 10)) ∧
    PureKuratowski.PairMember M a quotient (env (families 11)) ∧
    PureKuratowski.PairMember M a nonidentity (env (families 12)) ∧
    PureKuratowski.PairMember M a high (env (families 13)) ∧
    PureKuratowski.PairMember M a detector (env (families 14)) ∧
    PureKuratowski.PairMember M a patternOrder (env (families 15))

def fields {k : Nat} (families : Fin 16 → Fin k) (a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder : Fin k) : Project.Formula 1 k :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 0) a root))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 1) a chain))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 2) a codes))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 3) a order))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 4) a ranks))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 5) a selection))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 6) a rankBound))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 7) a labelSet))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 8) a tab))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 9) a r))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 10) a germGroup))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 11) a quotient))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 12) a nonidentity))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 13) a high))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (families 14) a detector))
    (ProjectSyntax.encode id (Source.SetLanguage.edge (families 15) a patternOrder)))))))))))))))))

theorem fields_freeClosed {k : Nat} (families : Fin 16 → Fin k) (a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder : Fin k) :
    (fields families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder).FreeClosed := by
  simp -implicitDefEqProofs [fields,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem fields_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (families : Fin 16 → Fin k)
    (a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder : Fin k) :
    Project.Formula.satisfies env (fields families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder) ↔
      Fields env.bound families (env.bound a) (env.bound root) (env.bound chain) (env.bound codes) (env.bound order) (env.bound ranks) (env.bound selection) (env.bound rankBound) (env.bound labelSet) (env.bound tab) (env.bound r) (env.bound germGroup) (env.bound quotient) (env.bound nonidentity) (env.bound high) (env.bound detector) (env.bound patternOrder) := by
  simp only [fields,Fields,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def Functions {k : Nat} (env : Fin k → M.Carrier .set) (families : Fin 16 → Fin k) (Q : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn Q (env (families 0)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 1)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 2)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 3)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 4)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 5)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 6)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 7)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 8)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 9)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 10)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 11)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 12)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 13)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 14)) ∧
    ForcingConditionGraphs.FunctionOn Q (env (families 15))

def functions {k : Nat} (families : Fin 16 → Fin k) (Q : Fin k) : Project.Formula 1 k :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 0) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 1) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 2) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 3) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 4) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 5) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 6) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 7) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 8) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 9) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 10) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 11) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 12) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 13) Q))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 14) Q))
    (ProjectSyntax.encode id (Source.SetLanguage.functionOn (families 15) Q)))))))))))))))))

theorem functions_freeClosed {k : Nat} (families : Fin 16 → Fin k) (Q : Fin k) :
    (functions families Q).FreeClosed := by
  simp -implicitDefEqProofs [functions,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem functions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (families : Fin 16 → Fin k) (Q : Fin k) :
    Project.Formula.satisfies env (functions families Q) ↔ Functions env.bound families (env.bound Q) := by
  simp only [functions,Functions,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M)]
  rfl

def context {k : Nat} (env : Fin k → M.Carrier .set)
    (a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder : M.Carrier .set) : Fin (k+17) → M.Carrier .set :=
  Fin.cases patternOrder (Fin.cases detector (Fin.cases high (Fin.cases nonidentity (Fin.cases quotient (Fin.cases germGroup (Fin.cases r (Fin.cases tab (Fin.cases labelSet (Fin.cases rankBound (Fin.cases selection (Fin.cases ranks (Fin.cases order (Fin.cases codes (Fin.cases chain (Fin.cases root (Fin.cases a (env)))))))))))))))))

def Assigned (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q : Fin k) (families : Fin 16 → Fin k) (d vertex label tau : M.Carrier .set) : Prop :=
  let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  ∃ a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder, (Project.FirstOrderSemantics.reduct M).mem a (env Q) ∧
    Fields env families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder ∧
    OrbitAssignment hM (context env a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder) (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) 15 (up w) 14 13 12 11 10 (up top) 9 8 7 6 (up K) (up B) (up zero) 5 4 3 2 1 0 d vertex label tau

def assigned {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q : Fin k)
    (families : Fin 16 → Fin k) (d vertex label tau : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE ((.conj (.mem (.bound 16) (.bound (up Q)))
    (.conj (fields (fun i => up (families i)) 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)
      (orbitAssignment (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) 15 (up w) 14 13 12 11 10 (up top) 9 8 7 6 (up K) (up B) (up zero) 5 4 3 2 1 0 id (up d) (up vertex) (up label) (up tau)))))))))))))))))))))

theorem assigned_freeClosed {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E w top K B zero Q : Fin k)
    (families : Fin 16 → Fin k) (d vertex label tau : Fin k) :
    (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau).FreeClosed := by
  simp -implicitDefEqProofs [assigned,Definitional.Formula.FreeClosed,
    fields_freeClosed,ForcingOrbitAssignment.orbitAssignment_freeClosed]

theorem assigned_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q : Fin k) (families : Fin 16 → Fin k) (d vertex label tau : Fin k) :
    Project.Formula.satisfies env (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau) ↔
      Assigned hM env.bound rho I G F mul q bound labels E w top K B zero Q families (env.bound d) (env.bound vertex) (env.bound label) (env.bound tau) := by
  simp only [assigned,Assigned,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,fields_semantics hM,
    ForcingOrbitAssignment.orbitAssignment_semantics hM]
  rfl

theorem assigned_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q : Fin k) (families : Fin 16 → Fin k) (d vertex label tau : M.Carrier .set) :
    Assigned hM other (fun j => base (rho j)) (base I) (base G) (base F) (base mul) (base q) (base bound) (base labels) (base E) (base w) (base top) (base K) (base B) (base zero) (base Q) (fun i => base (families i)) d vertex label tau ↔
      Assigned hM env rho I G F mul q bound labels E w top K B zero Q families d vertex label tau := by
  let upK : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let upN : Fin n → Fin (n+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let lifted : Fin (k+17) → Fin (n+17) := Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (Fin.cases 4 (Fin.cases 5 (Fin.cases 6 (Fin.cases 7 (Fin.cases 8 (Fin.cases 9 (Fin.cases 10 (Fin.cases 11 (Fin.cases 12 (Fin.cases 13 (Fin.cases 14 (Fin.cases 15 (Fin.cases 16 ((fun i => upN (base i)))))))))))))))))))
  have hCtx (a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder : M.Carrier .set) (i : Fin (k+17)) :
      context other a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder (lifted i) = context env a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder i := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (he))))))))))))))))) i
  have hLocal (a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder : M.Carrier .set) :
      OrbitAssignment hM (context other a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder) (fun j => upN (base (rho j))) (upN (base I)) (upN (base G)) (upN (base F)) (upN (base mul)) (upN (base q)) (upN (base bound)) (upN (base labels)) (upN (base E)) 15 (upN (base w)) 14 13 12 11 10 (upN (base top)) 9 8 7 6 (upN (base K)) (upN (base B)) (upN (base zero)) 5 4 3 2 1 0 d vertex label tau ↔
      OrbitAssignment hM (context env a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder) (fun j => upK (rho j)) (upK I) (upK G) (upK F) (upK mul) (upK q) (upK bound) (upK labels) (upK E) 15 (upK w) 14 13 12 11 10 (upK top) 9 8 7 6 (upK K) (upK B) (upK zero) 5 4 3 2 1 0 d vertex label tau := by
    exact ForcingOrbitRepresentativeDensity.orbitAssignment_reindex hM (context env a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder) (context other a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder) lifted (hCtx a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder) (fun j => upK (rho j)) (upK I) (upK G) (upK F) (upK mul) (upK q) (upK bound) (upK labels) (upK E) 15 (upK w) 14 13 12 11 10 (upK top) 9 8 7 6 (upK K) (upK B) (upK zero) 5 4 3 2 1 0 d vertex label tau
  constructor
  · rintro ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,ha,hFields,hOrbit⟩
    exact ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,by simpa only [he] using ha,
      by simpa only [Fields,he] using hFields,(hLocal a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder).mp hOrbit⟩
  · rintro ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,ha,hFields,hOrbit⟩
    exact ⟨a,root,chain,codes,order,ranks,selection,rankBound,labelSet,tab,r,germGroup,quotient,nonidentity,high,detector,patternOrder,by simpa only [he] using ha,
      by simpa only [Fields,he] using hFields,(hLocal a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder).mpr hOrbit⟩

theorem context_orbit (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder a : Fin k) (d vertex label tau : M.Carrier .set) :
    (let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
     OrbitAssignment hM (context env (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder)) (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) 15 (up w) 14 13 12 11 10 (up top) 9 8 7 6 (up K) (up B) (up zero) 5 4 3 2 1 0 d vertex label tau) ↔
      OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau := by
  let other := context env (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder)
  let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let collapse : Fin (k+17) → Fin k := Fin.cases patternOrder (Fin.cases detector (Fin.cases high (Fin.cases nonidentity (Fin.cases quotient (Fin.cases germGroup (Fin.cases r (Fin.cases tab (Fin.cases labelSet (Fin.cases rankBound (Fin.cases selection (Fin.cases ranks (Fin.cases order (Fin.cases codes (Fin.cases chain (Fin.cases root (Fin.cases a (id)))))))))))))))))
  have he (i : Fin (k+17)) : env (collapse i) = other i := by
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl ((fun _ => rfl)))))))))))))))))) i
  exact (ForcingOrbitRepresentativeDensity.orbitAssignment_reindex hM other env collapse he (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) 15 (up w) 14 13 12 11 10 (up top) 9 8 7 6 (up K) (up B) (up zero) 5 4 3 2 1 0 d vertex label tau).symm

theorem assigned_intro (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder Q a : Fin k)
    (families : Fin 16 → Fin k) (d vertex label tau : M.Carrier .set)
    (ha : (Project.FirstOrderSemantics.reduct M).mem (env a) (env Q))
    (hFields : Fields env families (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau) :
    Assigned hM env rho I G F mul q bound labels E w top K B zero Q families d vertex label tau := by
  exact ⟨env a,env root,env chain,env codes,env order,env ranks,env selection,env rankBound,env labelSet,env tab,env r,env germGroup,env quotient,env nonidentity,env high,env detector,env patternOrder,ha,hFields,
    (context_orbit hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder a d vertex label tau).mpr h⟩

def Germs (D I mul q roots germs : M.Carrier .set) : Prop := ∀ a root germ,
  PureKuratowski.PairMember M a root roots → PureKuratowski.PairMember M a germ germs →
    ConstructionGermCosets.Carrier D I mul q root germ

def germs {k : Nat} (D I mul q roots germs : Fin k) : Project.Formula 1 k :=
  .forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ 2 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge germs.succ.succ.succ 2 0))
      (ConstructionGermCosets.carrier D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ 1 0)))))

theorem germs_freeClosed {k : Nat} (D I mul q roots germFamily : Fin k) :
    (germs D I mul q roots germFamily).FreeClosed := by
  simp -implicitDefEqProofs [germs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionGermCosets.carrier_freeClosed]

theorem germs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (D I mul q roots germFamily : Fin k) :
    Project.Formula.satisfies env (germs D I mul q roots germFamily) ↔
      Germs (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound roots) (env.bound germFamily) := by
  simp only [germs,Germs,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionGermCosets.carrier_semantics hM]
  rfl

theorem assigned_iff_at (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau : Fin k)
    (families : Fin 16 → Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hVertices : ConstructionComponentCarrier.Carrier (env (rho 0)) (env I) (env mul) (env q) (env vertices))
    (hQuotient : ForcingOrbitQuotient.Classes (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env Q))
    (hProjection : ForcingOrbitQuotient.Projection (env (rho 0)) (env I) (env mul) (env q) (env vertices) (env pr))
    (hReps : ConstructionGermDetectors.Representatives (env vertices) (env Q) (env (families 0)))
    (hChains : ForcingOrbitChains.Family (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env vertices) (env Q) (env (families 0)) (env (families 1)))
    (hFunctions : Functions env families (env Q))
    (hGerms : Germs (env (rho 0)) (env I) (env mul) (env q) (env (families 0)) (env (families 10)))
    (hIndex : PureKuratowski.PairMember M (env vertex) (env a) (env pr))
    (hFields : Fields env families (env a) (env root) (env chain) (env codes) (env order) (env ranks) (env selection) (env rankBound) (env labelSet) (env tab) (env r) (env germGroup) (env quotient) (env nonidentity) (env high) (env detector) (env patternOrder)) :
    Assigned hM env rho I G F mul q bound labels E w top K B zero Q families (env d) (env vertex) (env label) (env tau) ↔
      OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau) := by
  constructor
  · rintro ⟨b,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,hb,hValues,hOrbit⟩
    obtain ⟨chosenRoot,hChosenRoot,hChosenChain⟩ := hChains.2 b x1 hValues.2.1
    have hRootEq := ForcingConditionGraphs.function_unique hFunctions.1 hChosenRoot hValues.1
    have hChain := hRootEq ▸ hChosenChain
    have hGerm := hGerms b x0 x10 hValues.1 hValues.2.2.2.2.2.2.2.2.2.2.1
    let other := context env b x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
    let up : Fin k → Fin (k+17) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    have hSame := ForcingOrbitIndex.orbitAssignment_index hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) 15 (up w) 14 13 12 11 10 (up top) 9 8 7 6 (up K) (up B) (up zero) 5 4 3 2 1 0 (up one) (up vertices) (up Q) (up pr) (up (families 0)) 16 (up a) (env d) (env vertex) (env label) (env tau)
      hm hJ hw hChain hq hGerm hVertices hQuotient hProjection hReps hValues.1 hIndex hOrbit
    change b = env a at hSame
    have hValuesAt : Fields env families (env a) x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 := hSame ▸ hValues
    have he0 := ForcingConditionGraphs.function_unique hFunctions.1 hValuesAt.1 hFields.1
    have he1 := ForcingConditionGraphs.function_unique hFunctions.2.1 hValuesAt.2.1 hFields.2.1
    have he2 := ForcingConditionGraphs.function_unique hFunctions.2.2.1 hValuesAt.2.2.1 hFields.2.2.1
    have he3 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.1 hValuesAt.2.2.2.1 hFields.2.2.2.1
    have he4 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.1 hValuesAt.2.2.2.2.1 hFields.2.2.2.2.1
    have he5 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.1 hFields.2.2.2.2.2.1
    have he6 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.1
    have he7 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.1
    have he8 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.1
    have he9 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.2.1
    have he10 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.2.2.1
    have he11 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.2.2.2.1
    have he12 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.2.2.2.2.1
    have he13 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have he14 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hValuesAt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hFields.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have he15 := ForcingConditionGraphs.function_unique hFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hValuesAt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hFields.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact (context_orbit hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder a (env d) (env vertex) (env label) (env tau)).mp (by
      simpa only [hSame,he0,he1,he2,he3,he4,he5,he6,he7,he8,he9,he10,he11,he12,he13,he14,he15] using hOrbit)
  · intro hOrbit
    exact ⟨env a,env root,env chain,env codes,env order,env ranks,env selection,env rankBound,env labelSet,env tab,env r,env germGroup,env quotient,env nonidentity,env high,env detector,env patternOrder,ForcingConditionGraphs.function_input hFunctions.1 hFields.1,hFields,
      (context_orbit hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder a (env d) (env vertex) (env label) (env tau)).mpr hOrbit⟩

def canonicalSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionComponentCarrier.carrier (rho 0) I mul q vertices)
    (.imp (ForcingOrbitQuotient.classes (rho 0) I mul q vertices Q)
    (.imp (ForcingOrbitQuotient.projection (rho 0) I mul q vertices pr)
    (.imp (ConstructionGermDetectors.representatives vertices Q (families 0))
    (.imp (ForcingOrbitChains.family w (rho 0) I mul q zero vertices Q (families 0) (families 1))
    (.imp (functions families Q)
    (.imp (germs (rho 0) I mul q (families 0) (families 10))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr vertex a))
    (.imp (fields families a root chain codes order ranks selection rankBound labelSet tab r germGroup quotient nonidentity high detector patternOrder)
      (.iff (assigned rho I G F mul q bound labels E w top K B zero Q families d vertex label tau)
        (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,
      ForcingOrbitQuotient.classes_freeClosed,ForcingOrbitQuotient.projection_freeClosed,
      ConstructionGermDetectors.representatives_freeClosed,ForcingOrbitChains.family_freeClosed,
      functions_freeClosed,germs_freeClosed,fields_freeClosed,assigned_freeClosed,ForcingOrbitAssignment.orbitAssignment_freeClosed]

theorem canonical_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (canonicalSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,
    ForcingOrbitQuotient.classes_semantics hM,ForcingOrbitQuotient.projection_semantics hM,
    ConstructionGermDetectors.representatives_semantics hM,ForcingOrbitChains.family_semantics hM,
    functions_semantics hM,germs_semantics hM,KuratowskiZF.source_edge,fields_semantics hM,
    assigned_semantics hM,ForcingOrbitAssignment.orbitAssignment_semantics hM]
  exact assigned_iff_at hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau families

theorem canonical_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (canonicalSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau families)) := by
  apply ModelTransfer.derives
  intro M hM
  exact canonical_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices Q pr a d vertex label tau families hM

end PPAC.Migration.ForcingAssigned
