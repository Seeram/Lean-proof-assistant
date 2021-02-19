import order.lattice
variables { L : Type* } [ lattice L]

set_option old_structure_cmd true

structure sublattice ( L : Type* ) [lattice L] :=
  ( carrier : set L)
  ( inf_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊓ b ∈ carrier )
  ( sup_mem'  {a b : L} : a ∈ carrier → b ∈ carrier → a ⊔ b ∈ carrier )

namespace sublattice

instance : has_coe ( sublattice L ) (set L)
:=
  { coe := sublattice.carrier }

instance : has_mem L ( sublattice L )
:=
  ⟨ λ m S, m ∈ ( S : set L) ⟩

instance : has_coe_to_sort ( sublattice L )
:=
  ⟨ Type*, λ S, { x : L // x ∈ S } ⟩

lemma mem_coe {SL : sublattice L} {x : L} :
  x ∈ SL.carrier ↔ x ∈ SL
:=
  iff.rfl

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

variable (SL)

theorem inf_mem {a b : L} :
  a ∈ SL → b ∈ SL → a ⊓ b ∈ SL
:=
  sublattice.inf_mem' SL

theorem sup_mem {a b : L} :
  a ∈ SL → b ∈ SL → a ⊔ b ∈ SL
:=
  sublattice.sup_mem' SL

lemma coe_injective :
  function.injective (coe : SL → L)
:=
  subtype.val_injective

instance to_lattice {M : Type*} [lattice L] (SL : sublattice L) :
  lattice L
:=
 SL.coe_injective.lattice

end sublattice


variables [lattice α] {a b c d : α}

open function

protected def function.injective.lattice { β : Type*}
  [ has_inf β ] [ has_sup β ]
  (f : β → α )
  (hf: injective f)
  (inf : ∀ a b, f(a ⊓ b) = f(a) ⊓ f(b) )
  (sup : ∀ a b, f(a ⊔ b) = f(a) ⊔ f(b) )
  :
  lattice α
:=
  {
    le           := ( ≤ ),
    le_refl      := λ x, le_refl x,
    le_trans     := λ x y z, le_trans,
    le_antisymm  := ,
--    le_antisymm  := λ x y hx hy, ,

    sup          := ( ⊔ ),
    le_sup_left  := λ x y, show x ≤ _, from ,
    le_sup_right := λ x y, show y ≤ _, from ,
    sup_le       := λ x y z hxz hyz, lfp_le $ sup_le (sup_le hxz hyz) (z.2.symm ▸ le_refl z.1),

    inf          := ( ⊓ ),
    inf_le_left  := λ x y, show _ ≤ x, from ,
    inf_le_right := λ x y, show _ ≤ y, from ,
    le_inf       := λ x y z hxy hxz, ,
  }

end lattice