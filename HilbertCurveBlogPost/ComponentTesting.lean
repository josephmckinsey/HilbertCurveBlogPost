import HilbertCurve.Pictures
import VersoBlog
import Std.Data.HashMap


open Verso Genre Blog
open Verso.Doc

section
open Verso Doc Elab ArgParse
open Lean
open Verso Output Html
open Template

#check (compare_hilbert_curves 2 3).toHtml

/--
Converts `ProofWidgets.Html` to `Verso.Output.Html`.

This is a partial implementation. It handles `element` and `text` nodes.
For `component` nodes, it currently just renders the children, as Verso
doesn't have a corresponding concept for interactive components.
-/
partial def pwHtmlToVersoHtml (h : ProofWidgets.Html) : Html :=
  match h with
  | .text s => .text true s
  | .element t attrs children =>
    let attrs' := attrs.map fun (k, v) => (k, ProofWidgets.escapeString v)
    let children' := children.map pwHtmlToVersoHtml
    .tag t attrs' (.seq children')
  | .component _hash _export _props children =>
    -- Verso doesn't have a notion of interactive components from ProofWidgets,
    -- so we just render the children as a fallback.
    .seq (children.map pwHtmlToVersoHtml)

@[block_component redBox]
def redBox : BlockComponent where
  toHtml id _data _goI goB contents := do
    saveCss (s!"#{id}:hover " ++ "{ border: 5px solid red; }")
    saveCss ".red-box { border: 2px solid red; }"
    pure {{<div class="red-box" id={{id}}>{{← contents.mapM goB}}</div>}}

@[directive_expander redBox]
def redBoxImpl : DirectiveExpander
  | args, stxs => do
    ArgParse.done.run args
    return #[← ``(Block.other (Blog.BlockExt.component $(quote `redBox) Json.null) #[$(← stxs.mapM elabBlock),*])]

#eval (DisplacementPlot 2 0).toString


def tes : String := "Hello $(name)."

#eval do
  let some substring := tes.toSubstring.findSubstr? "$(" | return
  println! { tes.toSubstring with stopPos := substring.startPos }
  println! { tes.toSubstring with startPos := substring.startPos }
  println! { tes.toSubstring with startPos := substring.startPos }.drop 2


/--
Replaces placeholders of the form `$(key)` in a string with values from a dictionary.

For example, `interpolate "Hello, $(name)!" (Std.HashMap.ofList [("name", "world")])`
returns `"Hello, world!"`.

If a key from a placeholder is not found in the dictionary, the placeholder is
left as is in the resulting string. This function does not handle nested placeholders.
-/
def interpolate (s : String) (dict : Std.HashMap String String) : String := Id.run do
  let mut out := ""
  let mut rest : Substring := s.toSubstring
  while !rest.isEmpty do
    if let some startParen := rest.findSubstr? "$(" then
      out := out ++ ({ rest with stopPos := startParen.startPos } : Substring).toString
      rest := { rest with startPos := startParen.startPos }.drop 2
      if let some endParen := rest.findSubstr? ")" then
        let k := { rest with stopPos := endParen.stopPos }.dropRight 1
        if let some v := dict.get? k.toString then
          out := out ++ v
        else
          out := out ++ s!"Could not find {k}"
        rest := { rest with startPos := endParen.stopPos }
      else
        out := out ++ rest.toString
        break
    else
      out := out ++ rest.toString
      break
  return out


/-- info: "Hello, my name is James." -/
#guard_msgs in
#eval interpolate "Hello, my name is $(name)." (Std.HashMap.ofList [("name", "James")])
