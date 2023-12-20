open Monad

module T (M: Monad)   : MonadTransformer 
  with type 'a t = 'a option M.t  and  type 'a old_t  := 'a M.t  = struct

  open MonadSyntax(M)

  type 'a t = 'a option M.t

  let pure x : 'a t = M.pure (Some x)

  let fmap (f:'a -> 'b) (x : 'a t) : 'b t =
    let+ x in match x with 
    | Some v -> Some (f v) 
    | _ -> None

  let apply (f:('a -> 'b) t) (x: 'a t) : 'b t = 
    let* f in match f with 
    | Some f -> fmap f x
    | None -> M.pure None

  
  let bind (x:'a t) (f : ('a -> 'b t)) : 'b t = 
    let* x in match x with 
    | Some x -> f x 
    | _ -> M.pure None

  let lift (x:'a M.t) : 'a t = let+ x in Some x
end


let list_of_option = function Some x -> [x] | None -> []

module M = T(MonadIdentity)