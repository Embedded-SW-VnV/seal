
type kind_t = Invariant | Stability

module type S =
  sig
    
    module Coeff : Osdp.Scalar.S
    module Poly : Osdp.Polynomial.S 
    module Mat : Osdp.Matrix.S

    type 'a t =
      {
        name : string;
        kind: kind_t;
        assumes: 'a option;
        poly : Poly.t;
        state_only : bool;
        (* bound : string *)
      }

  (*  val mk_inv: string -> 'a option -> Poly.t -> bool -> 'a t
    val mk_lyapunov: string -> 'a option -> Poly.t -> bool -> 'a t
    val pp_funs: 'a t -> (Format.formatter -> string -> unit) * (int) * (int)
   *)
  end

module Make
         (C: Osdp.Scalar.S)
         (P: Osdp.Polynomial.S with type Coeff.t = C.t)
         (M:Osdp.Matrix.S with type Coeff.t = C.t ) =
  struct
    module Coeff = C               
    module Poly = P
    module Mat = M 
  
    type 'a t =
      {
        name : string;
        kind: kind_t;
        assumes: 'a option;
        poly : Poly.t;
        state_only : bool;
        (* bound : string *)
      }
(*
    let mk_prop name assumes poly  state_only =
      {
        name = name;
        assumes = assumes;
        poly = poly;
        state_only  = state_only;
      }

    let mk_inv = mk_prop
    let mk_lyapunov = mk_prop

    let pp_funs pp_cons dynsys pp_lhs prop =
      let assumes =
        match prop.assumes with
        | None -> []
        | Some cons ->
           pp_cons
             dynsys.df
             (fun pp fmt x -> fprintf fmt "@@ @[<hov 2>assumes %a >= 0.;@]@ " pp x)
             pp_lhs
             fmt
             cons

           *)
  end
