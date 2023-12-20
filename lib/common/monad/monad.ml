module type Functor = sig 
  type 'a t 
  val fmap : ('a -> 'b) -> 'a t  -> 'b t
end

module type Applicative = sig
include Functor
  val pure : 'a -> 'a t  
  val apply : ('a -> 'b ) t -> 'a t -> 'b t
end 

module type Monad = sig
  include Applicative
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module type MonadTransformer = sig
  include Monad
  type 'a old_t
  val lift : 'a old_t -> 'a t
end

module MonadIdentity : Monad with type 'a t = 'a = struct
  type 'a t = 'a
  let pure x = x
  let fmap f x = f x
  let apply = fmap
  let bind x f = f x
end

module MonadOperator (M : Monad) = struct
  let (<*>) = M.apply
  let (<$>) = M.fmap
  let (<&>) = fun x f -> M.fmap f x
  let (>>=) = M.bind
  let (>>|) x f = x >>= fun x -> f x |> M.pure
end

module MonadSyntax (M : Monad ) = struct 
  open M
  open MonadOperator(M)
  let return = pure

  let (let*) : 'a M.t -> ('a -> 'b M.t) -> 'b M.t = M.bind

  let (and*) x y = 
    let* x = x in let* y = y in return (x,y)

  let (let+) : 'a M.t -> ('a -> 'b) -> 'b M.t = (>>|)
  let (and+) x y =
    let+ x = x in let+ y = y in return (x,y)

end