namespace Sum
  def HasMap {γ α β : Type} : (α → β) → Sum γ α → Sum γ β
  | f, Sum.inr val => Sum.inr (f val)
  | _, Sum.inl er  => Sum.inl er

  instance {α : Type} : Functor (Sum α) :=
  { map := @HasMap α }

  def HasSeq {γ α β : Type} (a : Sum γ (α → β)) (b : Unit → Sum γ α) : Sum γ β :=
  match a, b () with
  | Sum.inr f, Sum.inr x => Sum.inr (f x)
  | Sum.inl er, _ => Sum.inl er
  | _, Sum.inl er => Sum.inl er

  instance {α : Type} : Applicative (Sum α) :=
  { pure := λ x => Sum.inr x,
    seq := @HasSeq α }

  def HasBind {α β γ : Type} : Sum α β → (β → Sum α γ) → Sum α γ
  | Sum.inr val, f => f val
  | Sum.inl er,  _ => Sum.inl er

  instance {α : Type} : Monad (Sum α) :=
  { pure := λ x => Sum.inr x,
    bind := @HasBind α }

  @[matchPattern] abbrev fail {α β : Type} : α → Sum α β := Sum.inl
  @[matchPattern] abbrev ok {α β : Type} : β → Sum α β := Sum.inr
end Sum
