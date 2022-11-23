(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let version      = "u1"
let compile_date = ""

type output_t = StdOut | File of string
let out_to      = ref StdOut

let normalize_path p =
  (* We use the Unix subsystem to normalize a physical path (relative
     or absolute) and get rid of symbolic links, relative links (like
     ./ or ../ in the middle of the path; it's tricky but it
     works... *)
  (* Rq: Sys.getcwd () returns paths without '/' at the end *)
  let orig = Sys.getcwd () in
  Sys.chdir p;
  let res = Sys.getcwd () in
  Sys.chdir orig;
  res

let udoc_dft_path () =
  normalize_path (Filename.dirname Sys.executable_name)

let udoc_path  = ref (udoc_dft_path ())

type uoptions = {
  (* Title of the document *)
  title : string;

  (* Index/Toc options *)
  index       : bool;
  index_name  : string;
  multi_index : bool;
  toc         : bool;
  toc_depth   : int option;

  (* Header/Footer *)
  header_trailer   : bool;

  header_file      : string;
  header_file_spec : bool;
  footer_file      : string;
  footer_file_spec : bool;
}

let opts = ref {
    title       = "";
    index       = true;
    index_name  = "index";
    multi_index = false;
    toc         = false;
    toc_depth   = None;

    header_trailer   = true;
    header_file      = "";
    header_file_spec = false;
    footer_file      = "";
    footer_file_spec = false;
}

type coq_module = string

let output_dir = ref ""
let coqdoc_out f =
  if !output_dir <> "" && Filename.is_relative f then
    if not (Sys.file_exists !output_dir) then
      (Printf.eprintf "No such directory: %s\n" !output_dir; exit 1)
    else
      !output_dir ^ "/" ^ f
  else
    f

let with_outfile file f =
  try
    let out = open_out (coqdoc_out file) in
    f (Format.formatter_of_out_channel out);
    close_out out
  with | Sys_error s -> Printf.eprintf "%s\n" s; exit 1

