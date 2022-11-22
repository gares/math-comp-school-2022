(*******************************************************************************)
(*  v      *   The uDoc Document Generator for Coq                             *)
(* <O___,, *   Emilio J. Gallego Arias, Ècole de Mines, Paris - Copyright 2016 *)
(*   \VV/  *********************************************************************)
(*    //   *      This file is distributed under the terms of the              *)
(*         *       GNU General Public License Version 2 or later               *)
(*******************************************************************************)

(*******************************************************************************)
(* Document AST                                                                *)
(*                                                                             *)
(* We deviate from the CoqDoc model and will build an intermediate AST for     *)
(* pasing our .v files.                                                        *)
(*                                                                             *)
(*******************************************************************************)

type html = string

(* Theorem, Lemma, Etc... *)
(* type def_type = string *)

type coq =
  (* | Definition of def_type * string *)
  | Code   of string
  | Hidden of string

type box =
  | Print   of string
  | About   of string
  | Compute of string

type block =
  | Html   of html
  | Coq    of coq
  | Box    of box
  (* | Command of command *)

type doc = block list
