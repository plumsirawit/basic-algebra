class semigroup (α : Type u) extends HMul α α α where
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)

class has_one (α : Type u) where
  one : α

class monoid (α : Type u) extends semigroup α, has_one α where
  one_mul : ∀ a : α, one * a = a
  mul_one : ∀ a : α, a * one = a

class has_inv (α : Type u) extends semigroup α, HDiv α α α where
  inv : α → α
  inv_eq_div : ∀ a b : α, a / b = a * (inv a)

class group (α : Type u) extends monoid α, has_inv α where
  mul_left_inv : ∀ a : α, inv a * a = one

theorem inv_invo (g : group α) : ∀ a : α, g.inv (g.inv a) = a := by
  intro a
  have h := (g.mul_left_inv (g.inv a))
  have h2 : g.inv (g.inv a) * (g.inv a) * a = a := by {
    rw[h]
    apply g.one_mul
  }
  rw [g.mul_assoc] at h2
  rw [g.mul_left_inv a] at h2
  rw [g.mul_one] at h2
  exact h2

theorem inv_one_eq_one (g : group α) : g.inv g.one = g.one := by
  have h : (g.inv g.one) * g.one = g.one := g.mul_left_inv g.one
  have k := g.mul_one (g.inv g.one)
  rw [k] at h
  exact h

theorem mul_right_inv (g : group α) : ∀ a : α, a * (g.inv a) = g.one := by
  intro a
  have h := g.mul_left_inv (group.inv a)
  rw [inv_invo] at h
  exact h

class Set (α : Type u) where
  isMember : α → Prop

instance : Membership α (Set α) where
  mem := fun x s => s.isMember x

def set_eq (S T : Set α) := ∀ x : α, x ∈ S ↔ x ∈ T

class subgroup (G : group α) (S : Set α) where
  mul_mem : ∀ a b : α, a ∈ S → b ∈ S → a * b ∈ S
  one_mem : G.one ∈ S
  inv_mem : ∀ a : α, a ∈ S → G.inv a ∈ S

instance whole_group : Set α where
  isMember := fun _ => True

theorem self_is_subgroup {G : group α} : subgroup G whole_group := by
  have hmul_mem : ∀ a b : α, a ∈ whole_group → b ∈ whole_group → a * b ∈ whole_group := by
    rw [whole_group]
    intros a b _ _
    rw [Membership.mem, instMembershipSet]
    simp
  have hone_mem : G.one ∈ whole_group := by
    rw [Membership.mem, instMembershipSet]
    simp
    rw [Set.isMember, whole_group]
    simp
  have hinv_mem : ∀ a : α, a ∈ whole_group → G.inv a ∈ whole_group := by
    intros a _
    rw [Membership.mem, instMembershipSet]
    simp
    rw [Set.isMember, whole_group]
    simp
  exact {
    mul_mem := hmul_mem
    one_mem := hone_mem
    inv_mem := hinv_mem
  }

instance trivial_subgroup (G : group α) : Set α where
  isMember := fun x => x = G.one

theorem triv_is_subgroup {G : group α} : subgroup G (trivial_subgroup G) := by
  let H := trivial_subgroup G
  have hH : H = trivial_subgroup G := by simp
  rw [← hH]
  have hmul_mem : ∀ a b : α, a ∈ H → b ∈ H → a * b ∈ H := by
    intros a b ha hb
    rw [Membership.mem, instMembershipSet] at ha
    simp at ha
    rw [Set.isMember, trivial_subgroup] at ha
    simp at ha
    rw [Membership.mem, instMembershipSet] at hb
    simp at hb
    rw [Set.isMember, trivial_subgroup] at hb
    simp at hb
    rw [ha, hb]
    rw [G.mul_one]
    simp
    rw [trivial_subgroup, Membership.mem, instMembershipSet]
    simp
  have hone_mem : G.one ∈ H := by
    rw [Membership.mem, instMembershipSet]
    simp
    rw [Set.isMember, trivial_subgroup]
  have hinv_mem : ∀ a : α, a ∈ H → G.inv a ∈ H := by
    intros a ha
    rw [Membership.mem, instMembershipSet] at ha
    simp at ha
    rw [Set.isMember, trivial_subgroup] at ha
    simp at ha
    rw [ha]
    apply inv_one_eq_one
  exact {
    mul_mem := hmul_mem
    one_mem := hone_mem
    inv_mem := hinv_mem
  }

theorem mult_left (G : group α) (a b c : α) : b = c → a * b = a * c := by
  intro h
  rw [h]

theorem mult_right (G : group α) (a b c : α) : b = c → b * a = c * a := by
  intro h
  rw [h]

theorem cancel_left (G : group α) (a b c : α) : a * b = a * c → b = c := by
  intro h
  have h' := mult_left G (G.inv a) (a * b) (a * c) h
  rw [←G.mul_assoc, ←G.mul_assoc, G.mul_left_inv, G.one_mul, G.one_mul] at h'
  exact h'

theorem cancel_right (G : group α) (a b c : α) : b * a = c * a → b = c := by
  intro h
  have h' := mult_right G (G.inv a) (b * a) (c * a) h
  rw [G.mul_assoc, G.mul_assoc, mul_right_inv, G.mul_one, G.mul_one] at h'
  exact h'

class group_homomorphism (G : group α) (H : group β) where
  fn : α → β
  preserve_comp : ∀ g h : α, fn (g * h) = (fn g) * (fn h)

theorem hom_preserve_one (G : group α) (H : group β) (hom : group_homomorphism G H) : hom.fn G.one = H.one := by
  let φ := hom.fn
  have hphi : φ = hom.fn := by simp
  rw [← hphi]
  have hg : φ (G.one) = (φ G.one) * (φ G.one) := by
    rw [← hom.preserve_comp]
    conv =>
      left
      right
      rw [← G.mul_one G.one]
  conv at hg =>
    left
    rw [← H.mul_one (φ G.one)]
  have hh := (cancel_left H (φ G.one) _ _) hg
  rw [hh]

theorem hom_preserve_inv (G : group α) (H : group β) (hom : group_homomorphism G H) : ∀ g : α, hom.fn (G.inv g) = H.inv (hom.fn g) := by
  intro g
  let φ := hom.fn
  have hphi : φ = hom.fn := by simp
  rw [← hphi]
  apply (cancel_right H (φ g) _ _)
  rw [H.mul_left_inv]
  rw [← hom.preserve_comp (G.inv g) g]
  rw [← hphi]
  rw [G.mul_left_inv]
  apply hom_preserve_one

def kernel (G : group α) (H : group β) (φ : group_homomorphism G H) : Set α := {
  isMember := fun g => φ.fn g = H.one
}

def injective (fn : α → β) : Prop :=
  ∀ x y : α, fn x = fn y → x = y

theorem trivial_kernel_equiv_inj (G : group α) (H : group β) :
    ∀ hom : group_homomorphism G H, set_eq (kernel G H hom) (trivial_subgroup G) ↔
    injective hom.fn := by
  intros hom
  let φ := hom.fn
  have hphi : φ = hom.fn := by simp
  apply Iff.intro
  case mp =>
    intro h
    rw [injective]
    intros x y hinj
    rw [← hphi] at hinj
    have hh := mult_left H (H.inv (φ x)) _ _ hinj
    rw [H.mul_left_inv] at hh
    rw [←hom_preserve_inv] at hh
    rw [←hphi] at hh
    rw [←hom.preserve_comp] at hh
    have hker : (G.inv x * y) ∈ kernel G H hom := by
      rw [kernel, Membership.mem, instMembershipSet]
      simp
      rw [hh]
    have hsp := (h (G.inv x * y)).mp hker
    rw [trivial_subgroup, Membership.mem, instMembershipSet] at hsp
    simp at hsp
    have hmul := mult_left G x (group.inv x * y) G.one hsp
    rw [←G.mul_assoc] at hmul
    rw [mul_right_inv, G.one_mul, G.mul_one] at hmul
    rw [hmul]
  case mpr =>
    intro h
    rw [set_eq]
    intro x
    apply Iff.intro
    case mp =>
      intro hker
      rw [kernel, Membership.mem, instMembershipSet] at hker
      simp at hker
      rw [←hphi] at hker
      -- have hl := mult_left H (H.inv (φ x)) (φ x) H.one hker
      -- rw [←hom_preserve_inv, ←hphi, ←hom.preserve_comp, ←hphi, G.mul_left_inv] at hl
      rw [injective] at h
      have hinj := h G.one x
      rw [←hphi] at hinj
      rw [hphi, hom_preserve_one G H hom, ←hphi] at hinj
      have hl := hinj hker.symm
      rw [←hl]
      rw [Membership.mem, instMembershipSet]
      simp
      have hts : subgroup G (trivial_subgroup G) := triv_is_subgroup
      apply hts.one_mem
    case mpr =>
      intro hone
      rw [trivial_subgroup, Membership.mem, instMembershipSet] at hone
      simp at hone
      rw [hone]
      rw [kernel, Membership.mem, instMembershipSet]
      simp
      apply hom_preserve_one
