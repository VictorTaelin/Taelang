not
: ∀(b: Bool) Bool
= λb
  def T = λx(Bool)
  def if_true  = false
  def if_false = true
  (~b T if_true if_false)
