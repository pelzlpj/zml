(* Liveness analysis.
 *
 * This module provides a functorized iterative liveness solver which should be suitable
 * for determining variable lifetimes across a wide variety of problems.  In particular,
 * this is used during register allocation and also for automatically managing the lifetimes of
 * reference types.
 *)


module type CFG = sig
(** Description of a control-flow graph (i.e. storage for nodes of the graph, along with
    a functional description of the transitions between nodes). *)

  type t
  (** The graph nodes are stored in a lookup table of the following type *)

  module Id : Map.OrderedType
  (** The type of graph node identifiers *)

  module VSet : Set.S
  (** Sets of variables. *)

  val fold : (Id.t -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold f graph a] computes [(f idN ... (f id1 a) ...)] where id1...idN are the
  identifiers for graph [graph]. *)

  val successors : t -> Id.t -> Id.t list
  (** [successors graph id] computes the identifiers for CFG nodes which may immediately
  follow the node obtained by looking up [id] in the [graph]. *)

  val inputs : t -> Id.t -> VSet.t
  (** [inputs graph id] computes the set of variables which are treated as inputs by
  the CFG node obtained by looking up [id] in the [graph]. *)

  val outputs : t -> Id.t -> VSet.t
  (** [outputs graph id] computes the set of variables which are treated as outputs by
  the CFG node obtained by looking up [id] in the [graph]. *)
end


module Make = functor (Cfg : CFG) -> struct
  module VSet  = Cfg.VSet
  module IdMap = Map.Make(Cfg.Id)

  type t = {
    successors : Cfg.Id.t list;   (* List of identifiers for successor instructions *)
    gen        : VSet.t;          (* Set of variables which are inputs to this node *)
    kill       : VSet.t;          (* Set of variables which are outputs of this node *)
    live_in    : VSet.t;          (* Set of variables which are "live" before this instruction *)
    live_out   : VSet.t           (* Set of variables which are "live" after this instruction *)
  }

  let init_liveness_node (graph : Cfg.t) (id : Cfg.Id.t) : t = {
    successors = Cfg.successors graph id;
    gen        = Cfg.inputs graph id;
    kill       = Cfg.outputs graph id;
    live_in    = VSet.empty;
    live_out   = VSet.empty
  }

  let init_liveness (graph : Cfg.t) : t IdMap.t =
    Cfg.fold
      (fun id acc -> IdMap.add id (init_liveness_node graph id) acc)
      graph
      IdMap.empty

  let solve (graph : Cfg.t) : t IdMap.t =
    let rec fixpoint liveness =
      let next_liveness = IdMap.fold
        (fun i old_node acc ->
          let outputs_not_killed = VSet.diff old_node.live_out old_node.kill in
          let successor_inputs = List.fold_left
            (fun acc j -> VSet.union acc (IdMap.find j liveness).live_in)
            VSet.empty
            old_node.successors
          in
          let new_node = { old_node with
            live_in  = VSet.union old_node.gen outputs_not_killed;
            live_out = successor_inputs
          } in
          IdMap.add i new_node acc)
        liveness
        IdMap.empty
      in
      if next_liveness = liveness then liveness else fixpoint next_liveness
    in
    fixpoint (init_liveness graph)

end

