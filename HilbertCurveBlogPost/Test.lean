import VersoBlog
import HilbertCurveBlogPost.VersoProofWidget
import HilbertCurve.Pictures
open Verso Genre Blog
open Verso.Doc

set_option pp.rawOnError true


section
open Verso Doc Elab ArgParse
open Lean
open Verso Output Html
open Template

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

block_component gallery where
  toHtml id _data _goI goB contents := do
    saveCss (s!"#{id}:hover " ++ "{ border: 5px solid red; }")
    saveCss ".red-box { border: 2px solid red; }"
    pure {{<div class="red-box" id={{id}}>{{← contents.mapM goB}}</div>}}


/-

-- This fails with a parse error: WHY???
block_component image where
  toHtml id data _goI goB contents := do
    let .arr #[.str alt, .str url] := data
      | HtmlT.logError s!"Failed to deserialize {data}"
        pure .empty
    pure {{
      <div class="image-item" id={{id}}>
        <img href={{url}} alt={{alt}}>
        <div class="description">{{← contents.mapM goB}}</div>
      </div>
    }}

-/


@[directive_expander gallery]
def galleryImpl : DirectiveExpander
  | args, stxs => do
    ArgParse.done.run args
    let #[stx] := stxs
      | logErrorAt (mkNullNode stxs) "Expected one block"
        return #[← `(sorry)]
    let `(block| dl{ $item*}) := stx
      | throwErrorAt stx "Expected definition list"
    let items ← item.mapM getItem
    return #[← ``(Block.other (Blog.BlockExt.component $(quote `gallery) Json.null) #[$(items),*])]
where
  getItem : TSyntax `desc_item → DocElabM Term
    | `(desc_item|: $inls* => $desc $descs*) => do
      let #[inl] := inls.filter (fun
          | `(inline|$s:str) => s.getString.any (!·.isWhitespace)
          | _ => true)
        | throwErrorAt (mkNullNode inls) "Expected one inline"
      let `(inline|image($alt)($url)) := inl
        | throwErrorAt inl "Expected an image"
      `(Block.other (.component $(quote `image) (.arr #[$alt, $url])) #[$(← elabBlock desc), $(← descs.mapM elabBlock),*])
    | stx => throwErrorAt stx "Expected an image and description, got {stx}"

block_component +directive button' (onclick : String) where
  toHtml id _ _ goB contents := do
    saveJs <| "window.addEventListener('load', () => {" ++
      s!"document.getElementById('{id}')?.addEventListener('click', () => " ++
      "{ alert(" ++ onclick.quote ++ ");})});"
    pure {{
      <button id={{id}}>
        {{← contents.mapM goB}}
      </button>
    }}


inline_component button (onclick : String) where
  toHtml id _ goI contents := do
    saveJs <| "window.addEventListener('load', () => {" ++
      s!"document.getElementById('{id}')?.addEventListener('click', () => " ++
      "{ alert('hello');});});"
    pure {{
      <button id={{id}}>
        {{← contents.mapM goI}}
      </button>
    }}

@[role_expander button]
def buttonImpl : RoleExpander
  | args, contents => do
    let onclick ← ArgParse.run (.positional `onClick .string) args
    pure #[← ``(button $(quote onclick) #[$(← contents.mapM elabInline),*])]

end

open Verso.Output.Html in
def exampleHtml: Verso.Output.Html := {{
  <p>"Hi therE!"</p>
}}

def example2Html : ProofWidgets.Html := (
  ProofWidgets.Html.text "Hi"
)

def example2RealHtml : Verso.Output.Html := ProofWidgets.pwHtmlToVersoHtml example2Html

def Verso.Output.Html.addStyle (style : String): Verso.Output.Html → Verso.Output.Html
| .tag (name : String) (attrs : Array (String × String)) contents =>
  .tag name (attrs.push ("style", style)) contents
| x => x

def hilbert_example : Verso.Output.Html :=
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.compare_hilbert_curves 2 3).toHtml
  ).addStyle "max-width: 50%; margin: 0 auto; display: block;"



#doc (Page) "A Verso Blog" =>

Here's an example blog.


```leanInit demo
-- This block initializes a Lean context
```

```lean demo
def test : Nat := 3
```

Now we have another test:

```lean demo (error := true) (name := yVal)
#eval y
```
```leanOutput yVal
unknown identifier 'y'
```

hmm Inline {lean demo}`Nat`.

# {label test}[A Section with a Label]

How do I use a label? {ref test}[3].


:::redBox

It contains things. {button ""}[like a button! *hooray!*]

:::

::::blob exampleHtml
::::

:::button' "foo"

Here's a button

and a paragraph

:::

This should be an SVG:

::::blob hilbert_example
::::
