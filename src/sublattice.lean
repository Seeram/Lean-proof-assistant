import tactic
import order.lattice


variables { L : Type* } [ lattice L]

set_option old_structure_cmd true

structure sublattice ( L : Type* ) [lattice L] :=
  ( carrier : set L)
  ( inf_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier )
  ( sup_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier )

namespace sublattice

instance : has_coe ( sublattice L ) (set L) :=
  { coe := sublattice.carrier }

instance : has_mem L ( sublattice L ) :=
  ⟨ λ m S, m ∈ ( S : set L) ⟩

instance : has_coe_to_sort ( sublattice L ) :=
  ⟨ Type*, λ S, { x : L // x ∈ S } ⟩

lemma mem_coe {SL : sublattice L} {x : L} :
  x ∈ SL.carrier ↔ x ∈ SL
:=
  iff.rfl

end sublattice

protected lemma sublattice.exists {SL : sublattice L} {p : SL → Prop} :
  (∃ x : SL, p x) ↔ ∃ x ∈ SL, p ⟨x, ‹x ∈ SL›⟩
:=
  set_coe.exists

protected lemma sublattice.forall {SL : sublattice L} {p : SL → Prop} :
  (∀ x : SL, p x) ↔ ∀ x ∈ SL, p ⟨x, ‹x ∈ SL›⟩
:=
  set_coe.forall

theorem ext' ⦃ A B : sublattice L ⦄ (h : (A : set L) = B) :
  A = B
:=
  by cases A; cases B; congr'

theorem ext {A B : sublattice L} (h : ∀ x, x ∈ A ↔ x ∈ B) :
  A = B
:=
  ext' $ set.ext h

namespace sublattice

def copy (SL : sublattice L) (S : set L) (hs : S = SL) :
  sublattice L
:=
  {
    carrier := S,
    inf_mem' := hs.symm ▸ SL.inf_mem',
    sup_mem' := hs.symm ▸ SL.sup_mem'
  }

variable { SL : sublattice L}

lemma coe_copy {B : sublattice L} {A : set L} (hs : A = SL) :
  (SL.copy A hs : set L) = A
:=
  rfl

lemma copy_eq {s : set L} (hs : s = SL) :
  SL.copy s hs = SL
:=
  ext' hs

end sublattice

/-
class is_mul_hom {α β : Type*} [has_mul α] [has_mul β] (f : α → β) : Prop :=
(map_mul [] : ∀ x y, f (x * y) = f x * f y)
-/

/-
@[to_additive]
class is_monoid_hom [monoid α] [monoid β] (f : α → β) extends is_mul_hom f : Prop :=
(map_one [] : f 1 = 1)
-/

/-
namespace is_monoid_hom

variables [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

-- A monoid homomorphism preserves multiplication.
@[to_additive]
lemma map_mul (x y) : f (x * y) = f x * f y :=
is_mul_hom.map_mul f x y

end is_monoid_hom
-/

/-
namespace is_monoid_hom

variables [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]

/-- The identity map is a monoid homomorphism. -/
@[to_additive]
instance id : is_monoid_hom (@id α) := { map_one := rfl }

/-- The composite of two monoid homomorphisms is a monoid homomorphism. -/
@[to_additive] -- see Note [no instance on morphisms]
lemma comp {γ} [monoid γ] (g : β → γ) [is_monoid_hom g] :
  is_monoid_hom (g ∘ f) :=
{ map_one := show g _ = 1, by rw [map_one f, map_one g], ..is_mul_hom.comp _ _ }

end is_monoid_hom
-/