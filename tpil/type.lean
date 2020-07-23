namespace hidden

class inhabited (α : Type _) := (default : α)

#reduce default Prop
#print default

instance Prop_inhabited : inhabited Prop :=
⟨true⟩

instance bool_inhabited : inhabited bool :=
⟨tt⟩

instance nat_inhabited : inhabited nat :=
⟨0⟩

instance unit_inhabited : inhabited unit :=
⟨()⟩

def default (α : Type) [s : inhabited α] : α :=
@inhabited.default α s

instance prod_inhabited
  {α β : Type} [inhabited α] [inhabited β] : inhabited (prod α β) :=
⟨(default α, default β)⟩

#reduce default (nat × bool)

instance inhabited_fun (α : Type) {β : Type} [inhabited β] :
  inhabited (α → β) :=
⟨(λ a : α, default β)⟩

#check default (nat → nat × bool)
#reduce default (nat → nat × bool)

universes u v


instance prod_has_add {α : Type u} {β : Type v}
    [has_add α] [has_add β] :
  has_add (α × β) :=
⟨λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, ⟨a₁ + a₂, b₁ + b₂⟩⟩

#check (1, 2) + (3, 4)    -- ℕ × ℕ
#reduce  (1, 2) + (3, 4)  -- (4, 6)

end hidden

universe u

def list.add {α : Type u} [has_add α] :
  list α → list α → list α
| a [] := a
| [] b := b
| (a :: as) (b :: bs) := (a + b)::(list.add as bs)


instance {α : Type u} [has_add α] : has_add (list α) :=
  ⟨list.add⟩

#reduce [1,2,3] + [4,5,6,7,8]

set_option pp.implicit true

-- set_option trace.class_instances true

def step (a b x : ℕ) : ℕ :=
if x < a ∨ x > b then 0 else 1

#print definition step

def inhabited.set (α : Type*) : inhabited (set α) :=
by unfold set; apply_instance

#print inhabited.set

instance bool_to_Prop : has_coe bool Prop :=
⟨λ b, b = tt⟩

#reduce if tt then 3 else 5
#reduce if ff then 3 else 5

#print notation

def list.to_set {α : Type u} : list α → set α
| []     := ∅
| (h :: t) := {h} ∪ list.to_set t

instance list_to_set_coe (α : Type u) :
  has_coe (list α) (set α) :=
⟨list.to_set⟩

def s : set nat  := {1, 2}
def l : list nat := [3, 4]

#check s ∪  l -- set nat

structure Semigroup : Type (u+1) :=
(carrier : Type u)
(mul : carrier → carrier → carrier)
(mul_assoc : ∀ a b c : carrier,
               mul (mul a b) c = mul a (mul b c))

instance Semigroup_has_mul (S : Semigroup) :
  has_mul (S.carrier) :=
⟨S.mul⟩

#check Semigroup.carrier

instance Semigroup_to_sort : has_coe_to_sort Semigroup :=
{S := Type u, coe := λ S, S.carrier}

example (S : Semigroup) (a b c : S) :
  (a * b) * c = a * (b * c) :=
Semigroup.mul_assoc _ a b c

structure morphism (S1 S2 : Semigroup) :=
(mor : S1 → S2)
(resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b))

#check @morphism.mor

instance morphism_to_fun (S1 S2 : Semigroup) :
  has_coe_to_fun (morphism S1 S2) :=
{ F   := λ _, S1 → S2,
  coe := λ m, m.mor }

lemma resp_mul {S1 S2 : Semigroup}
    (f : morphism S1 S2) (a b : S1) :
  f (a * b) = f a * f b :=
f.resp_mul a b

theorem semi_assoc (S1 S2 : Semigroup) (f : morphism S1 S2) (a : S1) :
  f (a * a * a) = f a * f a * f a :=
calc
  f (a * a * a) = f (a * a) * f a : by rw [resp_mul f]
            ... = f a * f a * f a : by rw [resp_mul f]

#check semi_assoc
set_option pp.coercions false
#check semi_assoc