/- The unit law actually consumed by source height_bounds/cost_le_scale.
Reuse existing fraction density, natural associativity and scaled_equiv;
no general ordered-field or new division infrastructure. -/
import PPAC.Migration.ConstructionCutProduct

namespace PPAC.Migration.ConstructionCutProductUnit
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionFractionOrder ConstructionFractionDensity ConstructionRealCuts
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem fraction_one (hM : FirstOrder.Theory.Models M nativeZF) {w u one q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hq : Fraction w q) :
    ConstructionFractionProduct.Product hM w q u q := by
  obtain ⟨a,b,hq⟩ := hq
  exact ⟨a,b,one,one,a,b,hq,hu,hq,(mul_one hM hw hq.1 hu.1 hone).1,(mul_one hM hw hq.2.1 hu.1 hone).1⟩

/-- If p<q, a product q*r with r<1 lies strictly above p. Choose a
mediant t between p and q, then code r=t/q by native coordinate products. -/
theorem cofinal (hM : FirstOrder.Theory.Models M nativeZF) {w p q u one : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hu : Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one) (hq : Fraction w q)
    (hpq : Lt hM w p q) : ∃ r out, Fraction w r ∧ Lt hM w r u ∧
      ConstructionFractionProduct.Product hM w q r out ∧ Lt hM w p out := by
  obtain ⟨a,b,hq⟩ := hq
  obtain ⟨t,⟨c,d,ht⟩,hpt,htq⟩ := dense hM hw hpq
  have han := ConstructionFractionProduct.positive_numerator hM hw hq hpq
  obtain ⟨cb,hcbw,hcb⟩ := mul_exists hM hw ht.1 hq.2.1
  obtain ⟨da,hdaw,hda⟩ := mul_exists hM hw ht.2.1 hq.1
  have hdan := ConstructionFractionAddition.mul_nonempty hM hw ht.2.1 hq.1 ht.2.2.1 han hda
  obtain ⟨r,hrcode⟩ := KuratowskiZF.exists_code hM cb da
  have hr : Coordinates w r cb da := ⟨hcbw,hdaw,hdan,hrcode⟩
  have hcbda := (lt_iff_products hM hw ht hq hcb (mul_comm hM hw ht.2.1 hq.1 hda)).mp htq
  have hru := (lt_iff_products hM hw hr hu (mul_one hM hw hcbw hu.1 hone).1
    (mul_one hM hw hdaw hu.1 hone).2).mpr hcbda
  obtain ⟨n,hnw,hn⟩ := mul_exists hM hw hq.1 hcbw
  obtain ⟨den,hdenw,hden⟩ := mul_exists hM hw hq.2.1 hdaw
  obtain ⟨out,houtcode⟩ := KuratowskiZF.exists_code hM n den
  have hout : Coordinates w out n den := ⟨hnw,hdenw,
    ConstructionFractionAddition.mul_nonempty hM hw hq.2.1 hdaw hq.2.2.1 hdan hden,houtcode⟩
  obtain ⟨k,hkw,hk⟩ := mul_exists hM hw hq.1 hq.2.1
  obtain ⟨ck,_,hck⟩ := mul_exists hM hw ht.1 hkw
  obtain ⟨dk,_,hdk⟩ := mul_exists hM hw ht.2.1 hkw
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  have en := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord c ht.1) (ord b hq.2.1) (ord a hq.1) hcb (mul_comm hM hw hq.1 hq.2.1 hk) hck
    (mul_comm hM hw hq.1 hcbw hn)
  have ed := ZF.ordinalMultiplication_assoc hZF (KuratowskiZF.interpretation hM)
    (ord d ht.2.1) (ord a hq.1) (ord b hq.2.1) hda hk hdk (mul_comm hM hw hq.2.1 hdaw hden)
  have heq := ConstructionFractionDifference.scaled_equiv hM hw ht hout hkw (en ▸ hck) (ed ▸ hdk)
  exact ⟨r,out,⟨cb,da,hr⟩,hru,⟨a,b,cb,da,n,den,hq,hr,hout,hn,hden⟩,lt_le_trans hM hw hpt heq.1⟩

/-- Exact multiplicative identity on ALL internal nonnegative cuts. -/
theorem right_unit (hM : FirstOrder.Theory.Models M nativeZF) {w Q a u one unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit) (ha : Cut hM w Q a) : ConstructionCutProduct.Value hM w Q a unit a := by
  intro p
  constructor
  · intro hp
    obtain ⟨q,hqa,hpq⟩ := ha.2.2.1 p hp
    obtain ⟨r,out,hr,hru,hprod,hpo⟩ := cofinal hM hw hu hone ((hQ q).mp (ha.1 q hqa)) hpq
    exact ⟨ha.1 p hp,q,r,out,hqa,(hunit r).mpr ⟨(hQ r).mpr hr,hru⟩,hprod,hpo⟩
  · rintro ⟨_,q,r,out,hqa,hru,hprod,hpo⟩
    have hOneProd := fraction_one hM hw hu hone ((hQ q).mp (ha.1 q hqa))
    have hOutQ := ConstructionFractionProduct.product_left_mono hM hw
      (ConstructionFractionProduct.product_comm hM hw hprod)
      (ConstructionFractionProduct.product_comm hM hw hOneProd) ((hunit r).mp hru).2.1
    exact ha.2.1 p q hqa (lt_le_trans hM hw hpo hOutQ).1

/-- The exact scale*value<=scale consequence consumed by both source bounds. -/
theorem bounded_right (hM : FirstOrder.Theory.Models M nativeZF) {w Q a b c u one unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : Carrier w Q)
    (hu : Coordinates w u one one) (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : Principal hM w Q u unit) (ha : Cut hM w Q a)
    (hc : ConstructionCutProduct.Value hM w Q a b c) (hb : Subset b unit) : Subset c a :=
  ConstructionCutProduct.value_mono hc (right_unit hM hw hQ hu hone hunit ha) (fun _ h => h) hb

end PPAC.Migration.ConstructionCutProductUnit
