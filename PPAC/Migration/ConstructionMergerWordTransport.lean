/- Pinned ConservativeExtensions.Word.transport/transport_act/transport_mul/
transport_injective/transport_factors. Consumer: mergerSimulation_conservative.
Reuse the existing internal Raw graph and formula induction. Merger uses a
RIGHT action, unlike Probe's reduced-word left action. -/
import PPAC.Migration.ConstructionMergerCopiesMap
import PPAC.Migration.ConstructionProbeRawTransportSyntax

namespace PPAC.Migration.ConstructionMergerWordTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerPushout (Presentation)
open ConstructionProbeRaw (Raw Old Cons)
open ConstructionProbeRawTransport (Graph)
open ConstructionProbeAction (projected projected_range projected_indices)
open ConstructionProbeHomEvaluation (product_unique)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeConservative (Conservative)
open ConstructionProbePushout (Hom)
open ConstructionBaseMonoid (Divides)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (function_input function_unique)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}


def rightFactorsAt {m : Nat} (GN H y : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ 3 2)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ y.succ.succ.succ.succ 1)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramOrder.product GN.succ.succ.succ.succ 2 0 1))
    (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ 0 1))))))))))

theorem rightFactorsAt_freeClosed {m : Nat} (GN H y : Fin m) : (rightFactorsAt GN H y).FreeClosed := by
  simp -implicitDefEqProofs [rightFactorsAt, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem rightFactorsAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (GN H y : Fin m) :
    Project.Formula.satisfies env (rightFactorsAt GN H y) ↔ ∀ x fx fy q,
      PureKuratowski.PairMember M x fx (env.bound H) → PureKuratowski.PairMember M (env.bound y) fy (env.bound H) →
      Product (env.bound GN) fx q fy → ∃ r, PureKuratowski.PairMember M r q (env.bound H) := by
  simp only [rightFactorsAt, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, ForcingDiagramOrder.product_semantics (M := M)]
  rfl


def commonTargetAt {m : Nat} (W WN G GN H c : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ 2 0))
  (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ GN.succ.succ.succ.succ 1
  c.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ
  GN.succ.succ.succ.succ 0 c.succ.succ.succ.succ)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound
  W.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ.succ.succ 1 0)) (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  W.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ 5 1)) (.conj (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides W.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ 4 1))
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides WN.succ.succ.succ.succ.succ.succ
  GN.succ.succ.succ.succ.succ.succ 0 c.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem commonTargetAt_freeClosed {m : Nat} (W WN G GN H c : Fin m) : (commonTargetAt W WN G GN H c).FreeClosed := by
  simp -implicitDefEqProofs [commonTargetAt, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem commonTargetAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W WN G GN H c : Fin m) :
    Project.Formula.satisfies env (commonTargetAt W WN G GN H c) ↔ ∀ x y fx fy,
      PureKuratowski.PairMember M x fx (env.bound H) → PureKuratowski.PairMember M y fy (env.bound H) →
      Divides (env.bound WN) (env.bound GN) fx (env.bound c) → Divides (env.bound WN) (env.bound GN) fy (env.bound c) →
      ∃ k fk, (Project.FirstOrderSemantics.reduct M).mem k (env.bound W) ∧ PureKuratowski.PairMember M k fk (env.bound H) ∧
        Divides (env.bound W) (env.bound G) x k ∧ Divides (env.bound W) (env.bound G) y k ∧
        Divides (env.bound WN) (env.bound GN) fk (env.bound c) := by
  simp only [commonTargetAt, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

section Transport
variable {w n zero D mul e P C L projection A W T B G unit O roots : M.Carrier .set}
variable {N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN f g H : M.Carrier .set}
variable (hA : Presentation w n zero D mul e P C L projection A W T B G unit O roots)
variable (hB : Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
include hA hB

omit hB in
theorem old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H)
    {x fx q fq : M.Carrier .set} (hq : Old zero D x q) (hx : PureKuratowski.PairMember M x fx f) :
    PureKuratowski.PairMember M q fq H ↔ Old zero N fx fq := by
  constructor
  · intro hqf
    exact ConstructionProbeRawTransport.transport_old hM hz hf hq hx ((hGraph q fq).mp hqf)
  · intro hOld
    obtain ⟨r,hr,_⟩ := hH.1.2 q ((hA.word q).mpr (ConstructionProbeRaw.old_raw hM hz hzw hq))
    have hOldR := ConstructionProbeRawTransport.transport_old hM hz hf hq hx ((hGraph q r).mp hr)
    exact (ConstructionProbeRaw.old_unique hM hOldR hOld) ▸ hr

omit hB in
theorem snoc_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hf : MapsTo D N f) (hg : MapsTo L LN g) (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H)
    {s t q fq : M.Carrier .set} (hCons : Cons w D L s t q) :
    PureKuratowski.PairMember M q fq H ↔ ∃ gs ft,
      PureKuratowski.PairMember M s gs g ∧ PureKuratowski.PairMember M t ft H ∧ Cons w N LN gs ft fq := by
  constructor
  · intro hq
    obtain ⟨gs,hgs,_⟩ := hg.1.2 s (ConstructionProbeRawAction.cons_letter hCons)
    obtain ⟨ft,hft,_⟩ := hH.1.2 t ((hA.word t).mpr (ConstructionProbeRaw.cons_raw hCons).1)
    exact ⟨gs,ft,hgs,hft,ConstructionProbeRawTransport.transport_cons hM hw hf hg hCons hgs
      ((hGraph t ft).mp hft) ((hGraph q fq).mp hq)⟩
  · rintro ⟨gs,ft,hgs,hft,hFCons⟩
    obtain ⟨r,hr,_⟩ := hH.1.2 q ((hA.word q).mpr (ConstructionProbeRaw.cons_raw hCons).2)
    have hConsR := ConstructionProbeRawTransport.transport_cons hM hw hf hg hCons hgs
      ((hGraph t ft).mp hft) ((hGraph q r).mp hr)
    exact (ConstructionProbeRaw.cons_unique hM hw hConsR hFCons) ▸ hr

omit hA hB in
theorem transport_injective (hM : FirstOrder.Theory.Models M nativeZF)
    (hf : Injection D N f) (hg : Injection L LN g)
    (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H) : Injection W WN H := by
  refine ⟨hH,?_⟩
  intro x y z hx hy
  exact ConstructionProbeRawTransport.value_injective hM hf hg ((hGraph x z).mp hx) ((hGraph y z).mp hy)

theorem transport_act (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo L LN g) (hPres : PreservesProducts mul mulN f)
    (hEq : ConstructionMergerEvaluation.Equivariant A f g AN)
    (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H)
    {q x qx fq fx fqx : M.Carrier .set} (hAct : Product T q x qx)
    (hq : PureKuratowski.PairMember M q fq H) (hx : PureKuratowski.PairMember M x fx f)
    (hqx : PureKuratowski.PairMember M qx fqx H) : Product TN fq fx fqx := by
  apply (hB.word_action fq fx fqx).mpr
  refine ⟨hf.2 x fx hx,?_⟩
  rcases ((hA.word_action q x qx).mp hAct).2 with ⟨a,ax,hOld,hProd,hOut⟩ | ⟨s,t,sx,hCons,hProd,hOut⟩
  · obtain ⟨fa,hfa,_⟩ := hf.1.2 a hOld.1
    obtain ⟨fax,hfax,_⟩ := hf.1.2 ax hOut.1
    exact Or.inl ⟨fa,fax,(old_iff hA hM hz hzw hf hH hGraph hOld hfa).mp hq,
      hPres a x ax fa fx fax hProd hfa hx hfax,(old_iff hA hM hz hzw hf hH hGraph hOut hfax).mp hqx⟩
  · obtain ⟨gs,ft,hgs,hft,hConsN⟩ := (snoc_iff hA hM hw hf hg hH hGraph hCons).mp hq
    obtain ⟨gsx,ft',hgsx,hft',hOutN⟩ := (snoc_iff hA hM hw hf hg hH hGraph hOut).mp hqx
    have he := function_unique hH.1 hft' hft
    subst ft'
    exact Or.inr ⟨gs,ft,gsx,hConsN,hEq s x sx gs fx gsx hProd hgs hx hgsx,hOutN⟩

/-- Source transport_mul, using the existing multiplicativeAt formula and
internal Raw induction, not Lean induction on a host list of letters. -/
theorem transport_mul (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo L LN g) (hPres : PreservesProducts mul mulN f)
    (hEq : ConstructionMergerEvaluation.Equivariant A f g AN)
    (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H) : PreservesProducts G GN H := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    ⟨Fin.cases G (Fin.cases GN (fun _ => H)),fun _ => w⟩
  let p : Project.UnarySchema 3 := {
    body := ConstructionMergerEvaluation.multiplicativeAt 1 2 3 0
    freeClosed := ConstructionMergerEvaluation.multiplicativeAt_freeClosed .. }
  have he q : p.denote env q ↔ ∀ x xq fx fq fxq, Product G x q xq →
      PureKuratowski.PairMember M x fx H → PureKuratowski.PairMember M q fq H →
      PureKuratowski.PairMember M xq fxq H → Product GN fx fq fxq :=
    ConstructionMergerEvaluation.multiplicativeAt_semantics hM (env.push q) 1 2 3 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro a q hOld
    apply (he q).mpr
    intro x xq fx fq fxq hProd hx hq hxq
    obtain ⟨fa,hfa,_⟩ := hf.1.2 a hOld.1
    have hOldN := (old_iff hA hM hz hzw hf hH hGraph hOld hfa).mp hq
    exact (hB.product.1 fa fx fq fxq hOldN).mpr (transport_act hA hB hM hw hz hzw hf hg hPres hEq hH hGraph
      ((hA.product.1 a x q xq hOld).mp hProd) hx hfa hxq)) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro x xq fx fq fxq hProd hx hq hxq
    obtain ⟨xt,hxt,hOut⟩ := (hA.product.2 s t q x xq hCons).mp hProd
    obtain ⟨gs,ft,hgs,hft,hConsN⟩ := (snoc_iff hA hM hw hf hg hH hGraph hCons).mp hq
    obtain ⟨gs',fxt,hgs',hfxt,hOutN⟩ := (snoc_iff hA hM hw hf hg hH hGraph hOut).mp hxq
    have heq := function_unique hg.1 hgs' hgs
    subst gs'
    exact (hB.product.2 gs ft fq fx fxq hConsN).mpr ⟨fxt,(he t).mp ih x xt fx ft fxt hxt hx hft hfxt,hOutN⟩)
  intro x y z fx fy fz hProd hx hy hzv
  exact (he y).mp (hAll y ((hA.word y).mp (function_input hH.1 hy))) x z fx fy fz hProd hx hy hzv

theorem transport_hom (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Hom D N mul mulN e eN f) (hg : MapsTo L LN g)
    (hEq : ConstructionMergerEvaluation.Equivariant A f g AN)
    (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H) : Hom W WN G GN unit unitN H :=
  ⟨hH,(old_iff hA hM hz hzw hf.1 hH hGraph hA.old_unit hf.2.1).mpr hB.old_unit,
    transport_mul hA hB hM hw hz hzw hf.1 hg hf.2.2 hEq hH hGraph⟩


omit hB in
theorem old_preimage (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo L LN g) (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H)
    {q fq a : M.Carrier .set} (hMap : PureKuratowski.PairMember M q fq H) (hOld : Old zero N a fq) :
    ∃ x, Old zero D x q ∧ PureKuratowski.PairMember M x a f := by
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hA.word q).mp (function_input hH.1 hMap)) with ⟨x,hx⟩ | ⟨s,t,hCons⟩
  · obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx.1
    have he := ConstructionProbeRaw.old_injective ((old_iff hA hM hz hzw hf hH hGraph hx hfx).mp hMap) hOld
    exact ⟨x,hx,he ▸ hfx⟩
  · obtain ⟨gs,ft,_,_,hConsN⟩ := (snoc_iff hA hM hw hf hg hH hGraph hCons).mp hMap
    exact (ConstructionProbeRaw.old_ne_cons hz hOld hConsN).elim

omit hB in
theorem snoc_preimage (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo L LN g) (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H)
    {q fq gs ft : M.Carrier .set} (hMap : PureKuratowski.PairMember M q fq H) (hConsN : Cons w N LN gs ft fq) :
    ∃ s t, Cons w D L s t q ∧ PureKuratowski.PairMember M s gs g ∧ PureKuratowski.PairMember M t ft H := by
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hA.word q).mp (function_input hH.1 hMap)) with ⟨x,hx⟩ | ⟨s,t,hCons⟩
  · obtain ⟨fx,hfx,_⟩ := hf.1.2 x hx.1
    exact (ConstructionProbeRaw.old_ne_cons hz ((old_iff hA hM hz hzw hf hH hGraph hx hfx).mp hMap) hConsN).elim
  · obtain ⟨gs',ft',hgs,hft,hConsN'⟩ := (snoc_iff hA hM hw hf hg hH hGraph hCons).mp hMap
    obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hConsN' hConsN
    exact ⟨s,t,hCons,hgs,hft⟩

/-- Source transport_factors: a specific target right factor is the image of
an old word. Induction is on an internal result word, through rightFactorsAt. -/
theorem transport_factors (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Conservative D N mul mulN f) (hg : MapsTo L LN g)
    (hCopyFactors : ConstructionMergerCopiesMap.CopyFactors AN f g)
    (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H) :
    ConstructionProbeAlphabetMap.FactorConservation WN GN H := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 :=
    ⟨Fin.cases GN (fun _ => H),fun _ => w⟩
  let p : Project.UnarySchema 2 := {
    body := rightFactorsAt 1 2 0
    freeClosed := rightFactorsAt_freeClosed .. }
  have he y : p.denote env y ↔ ∀ x fx fy q, PureKuratowski.PairMember M x fx H →
      PureKuratowski.PairMember M y fy H → Product GN fx q fy → ∃ r, PureKuratowski.PairMember M r q H :=
    rightFactorsAt_semantics hM (env.push y) 1 2 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro b y hOldY
    apply (he y).mpr
    intro x fx fy q hx hy hProd
    obtain ⟨fb,hfb,_⟩ := hf.1.1.1.2 b hOldY.1
    have hOldFY := (old_iff hA hM hz hzw hf.1.1 hH hGraph hOldY hfb).mp hy
    obtain ⟨a,m,hOldFX,hOldQ,ham⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw
      hB.word hB.product_representatives hB.product_map hB.word_action hB.product hOldFY hProd
    obtain ⟨a0,hOldX,ha0⟩ := old_preimage hA hM hw hz hzw hf.1.1 hg hH hGraph hx hOldFX
    obtain ⟨m0,hm0⟩ := hf.2.1 a0 b m a fb ha0 hfb hOldQ.1 ham
    obtain ⟨r,hOldR⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) (function_input hf.1.1.1 hm0)
    exact ⟨r,(old_iff hA hM hz hzw hf.1.1 hH hGraph hOldR hm0).mpr hOldQ⟩) (by
    intro s t y hSnocY ih
    apply (he y).mpr
    intro x fx fy q hx hy hProd
    obtain ⟨gs,ft,hgs,hft,hSnocFY⟩ := (snoc_iff hA hM hw hf.1.1 hg hH hGraph hSnocY).mp hy
    have hqN := (projected_indices hB.product_representatives hB.product_map hProd).2
    rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hB.word q).mp hqN) with ⟨m,hOldQ⟩ | ⟨z,v,hSnocQ⟩
    · have hAct := (hB.word_action fx m fy).mp ((hB.product.1 m fx q fy hOldQ).mp hProd)
      rcases hAct.2 with ⟨a,am,_,_,hOldFY⟩ | ⟨a,pref,am,hSnocFX,ham,hSnocOut⟩
      · exact (ConstructionProbeRaw.old_ne_cons hz hOldFY hSnocFY).elim
      · obtain ⟨heS,heT⟩ := ConstructionProbeRaw.cons_injective hM hw hSnocOut hSnocFY
        subst am; subst pref
        obtain ⟨a0,pref0,_,ha0,_⟩ := snoc_preimage hA hM hw hz hzw hf.1.1 hg hH hGraph hx hSnocFX
        obtain ⟨m0,hm0⟩ := hCopyFactors a0 s a gs m ha0 hgs ham
        obtain ⟨r,hOldR⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) (function_input hf.1.1.1 hm0)
        exact ⟨r,(old_iff hA hM hz hzw hf.1.1 hH hGraph hOldR hm0).mpr hOldQ⟩
    · obtain ⟨out,hPrefix,hSnocOut⟩ := (hB.product.2 z v q fx fy hSnocQ).mp hProd
      obtain ⟨heS,heT⟩ := ConstructionProbeRaw.cons_injective hM hw hSnocOut hSnocFY
      subst z; subst out
      obtain ⟨r,hr⟩ := (he t).mp ih x fx ft v hx hft hPrefix
      obtain ⟨rs,hRS⟩ := ConstructionProbeRaw.exists_cons hM hw (ConstructionProbeRawAction.cons_letter hSnocY)
        ((hA.word r).mp (function_input hH.1 hr))
      exact ⟨rs,(snoc_iff hA hM hw hf.1.1 hg hH hGraph hRS).mpr ⟨gs,v,hgs,hr,hSnocQ⟩⟩)
  intro x y q fx fy hx hy _ hProd
  exact (he y).mp (hAll y ((hA.word y).mp (function_input hH.1 hy))) x fx fy q hx hy hProd

/-- Source transport_dvd_iff, retaining the actual reflected factor and exact
multiplication graphs; no new cancellation assumption on the word carrier. -/
theorem transport_dvd_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hH : Injection W WN H) (hMul : PreservesProducts G GN H)
    (hFactors : ConstructionProbeAlphabetMap.FactorConservation WN GN H) :
    ConstructionProbeAlphabetMap.DivisionReflection W WN G GN H := by
  intro x y fx fy hx hy
  constructor
  · rintro ⟨q,hq,hProd⟩
    obtain ⟨r,hr⟩ := hFactors x y q fx fy hx hy hq hProd
    obtain ⟨z,hz,hxz⟩ := projected hM hA.product_representatives hA.product_map
      (function_input hH.1.1 hx) (function_input hH.1.1 hr)
    obtain ⟨fz,hfz,_⟩ := hH.1.1.2 z hz
    have he := product_unique hM hB.product_map (hMul x r z fx q fz hxz hx hr hfz) hProd
    have hey : z = y := hH.2 z y fy (he ▸ hfz) hy
    exact ⟨r,function_input hH.1.1 hr,hey ▸ hxz⟩
  · rintro ⟨r,hr,hxr⟩
    obtain ⟨fr,hfr,_⟩ := hH.1.1.2 r hr
    exact ⟨fr,hH.1.2 r fr hfr,hMul x r y fx fr fy hxr hx hfr hy⟩


omit hB in
theorem old_divides_iff (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    {x y ox oy : M.Carrier .set} (hx : Old zero D x ox) (hy : Old zero D y oy) :
    Divides W G ox oy ↔ Divides D mul x y :=
  ConstructionMergerWordDivisibility.old_dvd_iff hM hw hz hzw hA.word hA.product_representatives
    hA.product_map hA.word_action hA.product (ConstructionProbeRaw.old_raw hM hz hzw hy) hx
    (ConstructionMergerWordDivisibility.leading_old hy)

omit hB in
theorem word_divides_refl {x : M.Carrier .set} (hx : (Project.FirstOrderSemantics.reduct M).mem x W) :
    Divides W G x x := ⟨unit,hA.unit_law.1,((hA.unit_law.2 x hx x).2).mpr rfl⟩

omit hB in
theorem word_divides_trans (hM : FirstOrder.Theory.Models M nativeZF) {x y z : M.Carrier .set}
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) (hxy : Divides W G x y) (hyz : Divides W G y z) :
    Divides W G x z := by
  obtain ⟨a,ha,hxa⟩ := hxy
  obtain ⟨b,hb,hyb⟩ := hyz
  obtain ⟨ab,hab,hp⟩ := projected hM hA.product_representatives hA.product_map ha hb
  exact ⟨ab,hab,(hA.associative x a b y ab z hx ha hb hxa hp).mp hyb⟩

/-- Source transport_common_below: formula induction on the arbitrary internal
TARGET word. Unequal lengths use division reflection; equal lengths consume the
actual Copies common-below theorem, without restricting the target upper bound. -/
theorem transport_common_below (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Conservative D N mul mulN f) (hg : MapsTo L LN g)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hCopyCommon : ConstructionMergerCopiesMap.CopyCommon D N L A AN g)
    (hH : Injection W WN H) (hGraph : Graph w D L LN f g H)
    (hDiv : ConstructionProbeAlphabetMap.DivisionReflection W WN G GN H) :
    ∀ c, Raw w N LN c → ∀ x y fx fy,
      PureKuratowski.PairMember M x fx H → PureKuratowski.PairMember M y fy H →
      Divides WN GN fx c → Divides WN GN fy c →
      ∃ k fk, (Project.FirstOrderSemantics.reduct M).mem k W ∧ PureKuratowski.PairMember M k fk H ∧
        Divides W G x k ∧ Divides W G y k ∧ Divides WN GN fk c := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    ⟨Fin.cases W (Fin.cases WN (Fin.cases G (Fin.cases GN (fun _ => H)))),fun _ => w⟩
  let p : Project.UnarySchema 5 := {
    body := commonTargetAt 1 2 3 4 5 0
    freeClosed := commonTargetAt_freeClosed .. }
  have he c : p.denote env c ↔ ∀ x y fx fy,
      PureKuratowski.PairMember M x fx H → PureKuratowski.PairMember M y fy H →
      Divides WN GN fx c → Divides WN GN fy c →
      ∃ k fk, (Project.FirstOrderSemantics.reduct M).mem k W ∧ PureKuratowski.PairMember M k fk H ∧
        Divides W G x k ∧ Divides W G y k ∧ Divides WN GN fk c :=
    commonTargetAt_semantics hM (env.push c) 1 2 3 4 5 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro m c hOldC
    apply (he c).mpr
    intro x y fx fy hx hy hxc hyc
    obtain ⟨qx,_,hpX⟩ := hxc
    obtain ⟨qy,_,hpY⟩ := hyc
    obtain ⟨a,ax,hOldFX,hOldQX,hax⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw
      hB.word hB.product_representatives hB.product_map hB.word_action hB.product hOldC hpX
    obtain ⟨b,bm,hOldFY,hOldQY,hby⟩ := ConstructionMergerWordMonoid.factors_of_old hM hw hz hzw
      hB.word hB.product_representatives hB.product_map hB.word_action hB.product hOldC hpY
    obtain ⟨a0,hOldX,ha0⟩ := old_preimage hA hM hw hz hzw hf.1.1 hg hH.1 hGraph hx hOldFX
    obtain ⟨b0,hOldY,hb0⟩ := old_preimage hA hM hw hz hzw hf.1.1 hg hH.1 hGraph hy hOldFY
    obtain ⟨k,fk,hk,hfk,hak,hbk,hfkm⟩ := ConstructionMergerCopiesMap.base_common_below hA.monoid hf hJoins ha0 hb0
      hOldC.1 ⟨ax,hOldQX.1,hax⟩ ⟨bm,hOldQY.1,hby⟩
    obtain ⟨ok,hOldK⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hk
    obtain ⟨ofk,hOldFK⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) (hf.1.1.2 k fk hfk)
    exact ⟨ok,ofk,(hA.word ok).mpr (ConstructionProbeRaw.old_raw hM hz hzw hOldK),
      (old_iff hA hM hz hzw hf.1.1 hH.1 hGraph hOldK hfk).mpr hOldFK,
      (old_divides_iff hA hM hw hz hzw hOldX hOldK).mpr hak,
      (old_divides_iff hA hM hw hz hzw hOldY hOldK).mpr hbk,
      (old_divides_iff hB hM hw hz hzw hOldFK hOldC).mpr hfkm⟩) (by
    intro d pref c hSnocC ih
    apply (he c).mpr
    intro x y fx fy hx hy hxc hyc
    have hDvd (v : M.Carrier .set) := ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hB.word hB.word_action hB.product (x := v) hSnocC
    rcases (hDvd fx).mp hxc with hxpref | ⟨dx,hEndX,hReachX⟩
    · rcases (hDvd fy).mp hyc with hypref | ⟨dy,hEndY,_⟩
      · obtain ⟨k,fk,hk,hfk,hxk,hyk,hfkpre⟩ := (he pref).mp ih x y fx fy hx hy hxpref hypref
        exact ⟨k,fk,hk,hfk,hxk,hyk,(hDvd fk).mpr (Or.inl hfkpre)⟩
      · have hxy : Divides WN GN fx fy :=
          (ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hB.word hB.word_action hB.product hEndY).mpr (Or.inl hxpref)
        exact ⟨y,fy,function_input hH.1.1 hy,hy,(hDiv x y fx fy hx hy).mp hxy,
          word_divides_refl hA (function_input hH.1.1 hy),hyc⟩
    · rcases (hDvd fy).mp hyc with hypref | ⟨dy,hEndY,hReachY⟩
      · have hyx : Divides WN GN fy fx :=
          (ConstructionMergerWordDivisibility.dvd_snoc_iff hM hw hz hzw hB.word hB.word_action hB.product hEndX).mpr (Or.inl hypref)
        exact ⟨x,fx,function_input hH.1.1 hx,hx,word_divides_refl hA (function_input hH.1.1 hx),
          (hDiv y x fy fx hy hx).mp hyx,hxc⟩
      · obtain ⟨a,xp,hSnocX,hga,hxp⟩ := snoc_preimage hA hM hw hz hzw hf.1.1 hg hH.1 hGraph hx hEndX
        obtain ⟨b,yp,hSnocY,hgb,hyp⟩ := snoc_preimage hA hM hw hz hzw hf.1.1 hg hH.1 hGraph hy hEndY
        have hep : xp = yp := hH.2 xp yp pref hxp hyp
        subst yp
        obtain ⟨j,gj,hj,hgj,haj,hbj,hgjd⟩ := hCopyCommon a b dx dy d hga hgb hReachX hReachY
        obtain ⟨k,hK⟩ := ConstructionProbeRaw.exists_cons hM hw hj ((hA.word xp).mp (function_input hH.1.1 hxp))
        obtain ⟨fk,hFK⟩ := ConstructionProbeRaw.exists_cons hM hw (hg.2 j gj hgj) (ConstructionProbeRaw.cons_raw hSnocC).1
        exact ⟨k,fk,(hA.word k).mpr (ConstructionProbeRaw.cons_raw hK).2,
          (snoc_iff hA hM hw hf.1.1 hg hH.1 hGraph hK).mpr ⟨gj,pref,hgj,hxp,hFK⟩,
          (ConstructionMergerWordDivisibility.snoc_dvd_snoc_iff hM hw hz hzw hA.word hA.word_action hA.product hSnocX hK).mpr (Or.inr ⟨rfl,haj⟩),
          (ConstructionMergerWordDivisibility.snoc_dvd_snoc_iff hM hw hz hzw hA.word hA.word_action hA.product hSnocY hK).mpr (Or.inr ⟨rfl,hbj⟩),
          (ConstructionMergerWordDivisibility.snoc_dvd_snoc_iff hM hw hz hzw hB.word hB.word_action hB.product hFK hSnocC).mpr (Or.inr ⟨rfl,hgjd⟩)⟩)
  intro c hc
  exact (he c).mp (hAll c hc)

/-- All four source Conservative fields for the actual internal Raw transport. -/
theorem transport_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Conservative D N mul mulN f) (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hCopy : ConstructionMergerCopiesMap.Laws D N L LN projection projectionN A AN f g)
    (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H) (hMul : PreservesProducts G GN H) :
    Conservative W WN G GN H := by
  have hInj := transport_injective hM hf.1 hCopy.1 hH hGraph
  have hFactors := transport_factors hA hB hM hw hz hzw hf hCopy.1.1 hCopy.2.2.2.2.1 hH hGraph
  have hDiv := transport_dvd_iff hA hB hM hInj hMul hFactors
  have hBelow := transport_common_below hA hB hM hw hz hzw hf hCopy.1.1 hJoins hCopy.2.2.2.2.2 hInj hGraph hDiv
  refine ⟨hInj,hFactors,?_,?_⟩
  · intro x y j fx fy fj hx hy hj hJoin c hc
    constructor
    · rintro ⟨hxc,hyc⟩
      obtain ⟨k,fk,hk,hfk,hxk,hyk,hfkc⟩ := hBelow c ((hB.word c).mp hc) x y fx fy hx hy hxc hyc
      exact word_divides_trans hB hM (hH.2 j fj hj) ((hDiv j k fj fk hj hfk).mpr ((hJoin k hk).mp ⟨hxk,hyk⟩)) hfkc
    · intro hfjc
      have hu := (hJoin j (function_input hH.1 hj)).mpr (word_divides_refl hA (function_input hH.1 hj))
      exact ⟨word_divides_trans hB hM (hH.2 x fx hx) ((hDiv x j fx fj hx hj).mpr hu.1) hfjc,
        word_divides_trans hB hM (hH.2 y fy hy) ((hDiv y j fy fj hy hj).mpr hu.2) hfjc⟩
  · intro x y fx fy hx hy hCommon
    obtain ⟨c,hc,hxc,hyc⟩ := hCommon
    obtain ⟨k,_,hk,_,hxk,hyk,_⟩ := hBelow c ((hB.word c).mp hc) x y fx fy hx hy hxc hyc
    exact ⟨k,hk,hxk,hyk⟩


/-- The existing pushout simulation and the literal Raw transport are the SAME
set graph, by old/snoc equations and the existing object agreement induction. -/
theorem raw_eq_simulation (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : MapsTo D N f) (hg : MapsTo L LN g)
    (hRep : ConstructionProbeLettersMapSyntax.RepresentativeLaw projection projectionN f g)
    (hH : MapsTo W WN H) (hGraph : Graph w D L LN f g H) {K : M.Carrier .set}
    (hK : Hom W WN G GN unit unitN K) (hComm : ConstructionProbePushout.SquareComm O f K ON)
    (hRoots : ConstructionProbeMappedPath.NodeMap roots K rootsN) : H = K := by
  have hKSnoc := ConstructionMergerPushout.simulation_snoc hM hA hB hw hz hzw hf hK hComm hRoots
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := ⟨Fin.cases H (fun _ => K),fun _ => w⟩
  let p : Project.UnarySchema 2 := {
    body := ConstructionProbeHomExt.agreeAt 0 1 2
    freeClosed := ConstructionProbeHomExt.agreeAt_freeClosed .. }
  have he q : p.denote env q ↔ ConstructionProbeHomExt.AgreeAt q H K :=
    ConstructionProbeHomExt.agreeAt_semantics hM (env.push q) 0 1 2
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro a q hOld
    apply (he q).mpr
    intro y z hy hzv
    obtain ⟨fa,hfa,_⟩ := hf.1.2 a hOld.1
    have hOldY := (old_iff hA hM hz hzw hf hH hGraph hOld hfa).mp hy
    have hOldZ := (hB.old_graph fa z).mp ((hComm a q fa z ((hA.old_graph a q).mpr hOld) hfa).mp hzv)
    exact ConstructionProbeRaw.old_unique hM hOldY hOldZ) (by
    intro c t q hCons ih
    apply (he q).mpr
    intro y z hy hzv
    obtain ⟨gc,ft,hgc,hft,hConsN⟩ := (snoc_iff hA hM hw hf hg hH hGraph hCons).mp hy
    obtain ⟨kt,hkt,_⟩ := hK.1.1.2 t ((hA.word t).mpr (ConstructionProbeRaw.cons_raw hCons).1)
    have het : ft = kt := (he t).mp ih ft kt hft hkt
    subst kt
    obtain ⟨i,a,_,ha,hic⟩ := ConstructionMergerCopies.representative hA.representatives hA.copies hA.projection_law
      (ConstructionProbeRawAction.cons_letter hCons)
    obtain ⟨fa,hfa,_⟩ := hf.1.2 a ha
    have hicN := (hRep i a fa c gc hic hfa).mp hgc
    exact function_unique hK.1.1 (hKSnoc i a fa c gc t ft q y hic hfa hicN hCons hkt hConsN) hzv)
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM W WN H).mp hH).1.1
    ((ForcingSupportSize.native_mapsTo hM W WN K).mp hK.1).1.1
  intro q y
  constructor
  · intro hy
    have hq := function_input hH.1 hy
    obtain ⟨z,hzv,_⟩ := hK.1.1.2 q hq
    exact ((he q).mp (hAll q ((hA.word q).mp hq)) y z hy hzv).symm ▸ hzv
  · intro hy
    have hq := function_input hK.1.1 hy
    obtain ⟨z,hzv,_⟩ := hH.1.2 q hq
    exact ((he q).mp (hAll q ((hA.word q).mp hq)) z y hzv hy) ▸ hzv

/-- Pinned mergerSimulation_conservative for the already constructed actual
simulation, not a new abstract map with a different codomain or presentation. -/
theorem simulation_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hOne : PureKuratowski.PairMember M e eN f)
    (hMap : ConstructionMergerPrescriptionMap.Mapped P f PN)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    {K : M.Carrier .set} (hK : Hom W WN G GN unit unitN K)
    (hComm : ConstructionProbePushout.SquareComm O f K ON)
    (hRoots : ConstructionProbeMappedPath.NodeMap roots K rootsN) : Conservative W WN G GN K := by
  obtain ⟨g,hCopy⟩ := ConstructionMergerCopiesMap.exists_system hM hA hB hf hPres hMap hJoins
  obtain ⟨H,hH,hGraph⟩ := ConstructionProbeRawTransportSyntax.exists_graph hM hf.1.1 hCopy.1.1 hA.word hB.word
  have hHom := transport_hom hA hB hM hw hz hzw ⟨hf.1.1,hOne,hPres⟩ hCopy.1.1 hCopy.2.2.2.1 hH hGraph
  have hMul := hHom.2.2
  have hCons := transport_conservative hA hB hM hw hz hzw hf hJoins hCopy hH hGraph hMul
  have he := raw_eq_simulation hA hB hM hw hz hzw hf.1.1 hCopy.1.1 hCopy.2.2.1 hH hGraph hK hComm hRoots
  exact he ▸ hCons

end Transport

/-- Reuse the existing complete producer, then certify conservation of its
actual induced map. All 24 sets/graphs remain internal existential outputs. -/
theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P N mulN eN f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hmN : ForcingDiagramPoset.LeftCancelMonoid N mulN eN)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hOne : PureKuratowski.PairMember M e eN f)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul) :
    ∃ PN C L projection A W T B G unit O roots CN LN projectionN AN WN TN BN GN unitN ON rootsN H,
      ConstructionMergerPrescriptionMap.Graph P f PN ∧
      Presentation w n zero D mul e P C L projection A W T B G unit O roots ∧
      Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN ∧
      Hom W WN G GN unit unitN H ∧ Conservative W WN G GN H ∧ ConstructionProbeMappedPath.NodeMap roots H rootsN ∧
      ConstructionMergerPushout.TransportSnoc w D L projection N LN projectionN f H ∧
      ConstructionProbePushout.IsPushout N W WN mulN G GN eN unit unitN O f H ON := by
  obtain ⟨PN,C,L,projection,A,W,T,B,G,unit,O,roots,CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,H,
    hGraph,hA,hB,hH,hRoots,hSnoc,hPush⟩ := ConstructionMergerPushout.exists_system hM hw hz hzw hm hmN hP hValid hf hPres hOne hJoins
  have hCons := simulation_conservative hA hB hM hw hz hzw hf hPres hOne
    (ConstructionMergerPrescriptionMap.mapped hM hGraph) hJoins hH hPush.1 hRoots
  exact ⟨PN,C,L,projection,A,W,T,B,G,unit,O,roots,CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,H,
    hGraph,hA,hB,hH,hCons,hRoots,hSnoc,hPush⟩

/-- Every constructed set and graph is existentially quantified inside the
pure-membership sentence, including both Merger carriers and the simulation. -/
def sourceSentence {m : Nat} (w n zero D mul e P N mulN eN f : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound
    zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid N mulN eN)) (.imp
    (ConstructionMergerRelations.prescription n D P) (.imp (ConstructionMergerRelations.valid n D mul P) (.imp
    (ConstructionProbeConservativeSyntax.conservative D N mul mulN f) (.imp
    (ConstructionProbeLiftHomSyntax.preservesProducts mul mulN f) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge f e eN)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionMergerPrescriptionMapSyntax.graph
    P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    23) (.conj (ConstructionMergerPushout.presentation
    w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    22 21 20 19 18 17 16 15 14 13 12) (.conj (ConstructionMergerPushout.presentation
    w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    23 11 10 9 8 7 6 5 4 3 2 1) (.conj (ConstructionProbePushoutSyntax.hom 18 7 15 4 14 3 0) (.conj (ConstructionProbeConservativeSyntax.conservative 18 7 15 4 0) (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap 12 0 1) (.conj (ConstructionMergerPushout.transportSnoc
    w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    21 20
    N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    10 9
    f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    0) (ConstructionProbePushoutSyntax.isPushout
    N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    18 7
    mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    15 4
    eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    14 3 13
    f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
    0 2)))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      Project.Formula.isOmega,
      Project.Formula.isEmpty,
      ConstructionMergerRelations.prescription_freeClosed,
      ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,
      ConstructionMergerPushout.presentation_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
      ConstructionMergerPushout.transportSnoc_freeClosed,
      ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem source_models {m : Nat} (w n zero D mul e P N mulN eN f : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w n zero D mul e P N mulN eN f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (sourceSentence w n zero D mul e P N mulN eN f)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionMergerRelations.prescription_semantics hM,
    ConstructionMergerRelations.valid_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,
    ConstructionMergerPushout.presentation_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ConstructionMergerPushout.transportSnoc_semantics hM,
    ConstructionProbePushoutSyntax.isPushout_semantics hM]
  exact exists_system hM

theorem source_kernel_certificate {m : Nat} (w n zero D mul e P N mulN eN f : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sourceSentence w n zero D mul e P N mulN eN f)) :=
  ModelTransfer.derives (fun _ hM => source_models w n zero D mul e P N mulN eN f hM)

end PPAC.Migration.ConstructionMergerWordTransport
