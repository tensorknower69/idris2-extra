module Extra.Pair

public export
data LLPair : Type -> Type -> Type where
  (#) : (1 _ : a) -> b -> LLPair a b

infixl 0 :>

public export
data Of : (a : Type) -> (b : Type) -> Type where
  (:>) : a -> Lazy b -> Of a b

export
Bifunctor Of where
  mapFst f (a :> b) = f a :> b
  mapSnd f (a :> b) = a :> f b
  bimap f g (a :> b) = f a :> g b

export
Functor (Of a) where
  map = mapSnd
