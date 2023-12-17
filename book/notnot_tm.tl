notnot_tm
: ∀(b: Bool) (Equal Bool (not (not b)) b)
= λb
  def T = λb(Equal Bool (not (not b)) b)
  def if_true  = (refl Bool true)
  def if_false = (refl Bool false)
  (b T if_true if_false)
