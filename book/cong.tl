cong
: ∀(A: *)
  ∀(B: *)
  ∀(a: A)
  ∀(b: A)
  ∀(f: ∀(x: A) B)
  ∀(e: (Equal A a b))
  (Equal B (f a) (f b))
= λA λB λa λb λf λe
  def T = λx(Equal B (f a) (f x))
  def if_refl = (refl B (f a))
  (e T if_refl)
