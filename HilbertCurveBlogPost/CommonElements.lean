import VersoBlog
import HilbertCurveBlogPost.VersoProofWidget
import HilbertCurve.Pictures

open Verso Genre Blog
open Verso.Doc
section
open Verso Doc Elab ArgParse
open Lean
open Verso Output Html
open Template

def Verso.Output.Html.addAttrs (attrList : Array (String × String)) : Verso.Output.Html → Verso.Output.Html
| .tag (name : String) (attrs : Array (String × String)) contents =>
  .tag name (attrList.append attrs) contents
| x => x


def hilbert_example : Verso.Output.Html :=
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.compare_hilbert_curves 2 3).toHtml
  ).addAttrs #[("style", "max-width: 25%; margin: 0 auto; display: block;")]


open Verso.Output.Html in
def hamster_alone : Verso.Output.Html := Verso.Output.Html.tag "img" #[
  ("src", "hilbertcurve/hamster_alone.svg"),
  ("alt", "Our hypothesized curve moving from left to right, depicted as a hamster on an arrow."),
  ("style", "max-width: 25%; margin: 0 auto; display: block;")
] (.text false "")

open Verso.Output.Html in
def hamster_together : Verso.Output.Html := Verso.Output.Html.tag "img" #[
  ("src", "hilbertcurve/hamster_together.svg"),
  ("alt", "How we put our curve together, depicted as 4 squares containing hamsters moving up, right, right, and down so that the hamster's back is 'in' the square."),
  ("style", "max-width: 50%; margin: 0 auto; display: block;")
] (.text false "")

def verso_hilbert_curve (i : ℕ) : Verso.Output.Html :=
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.hilbert_curve_svg i).toHtml
  ).addAttrs
    #[("alt", s!"A simple example of iteration {i} of the Hilbert Curve.")]

def hilbert_curve_123 : Verso.Output.Html :=
  .seq <| #[1, 2, 3, 4].map (fun i =>
  (verso_hilbert_curve i).addAttrs #[("width", "20%"), ("height", "20%"), ("viewBox", "0 0 400 400")])

def hilbert_curve_3 : Verso.Output.Html :=
  (verso_hilbert_curve 3).addAttrs
  #[("style", "max-width: 50%; margin: 0 auto; display: block;")]

#html (HilbertCurve.hilbert_curve_with_points 2).toHtml
#html (HilbertCurve.hilbert_curve_squares_svg 2).toHtml
#html (HilbertCurve.hilbert_curve_squares_svg 3).toHtml

def hilbert_curve_red_squares : Verso.Output.Html :=
  .seq <| #[1, 2, 3].map (fun i =>
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.hilbert_curve_with_points i (.abs 4)).toHtml
  ).addAttrs
    #[("width", "25%"), ("height", "25%"), ("viewBox", "0 0 400 400"),
    ("alt", "The 2nd iteration of the hilbert curve, where the curve connects squares.")])

def hilbert_curve_rainbow2 : Verso.Output.Html :=
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.hilbert_curve_squares_svg 2).toHtml
  ).addAttrs
    #[("style", "max-width: 50%; margin: 0 auto; display: block;"),
    ("alt", "The 2nd iteration of the hilbert curve, where the colors
    change from red, blue, etc, back to red.")]

def hilbert_curve_rainbow3 : Verso.Output.Html :=
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.hilbert_curve_squares_svg 3).toHtml
  ).addAttrs
    #[("style", "max-width: 50%; margin: 0 auto; display: block;"),
    ("alt", "The 3rd iteration of the hilbert curve, where the colors
    change from red, blue, etc, back to red. The colors haven't changed much since the 2nd iteration.")]

def hilbert_curve_comparison23 : Verso.Output.Html :=
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.compare_hilbert_curves 2 3 (.abs 6) (.abs 2)).toHtml
  ).addAttrs
    #[("style", "max-width: 60%; margin: 0 auto; display: block;"),
    ("alt", "A comparison of the 2nd to 3rd iteration of the hilbert curve.
    Many points line up, and points that don't are not too far away.")]

def hilbert_curve_comparison34 : Verso.Output.Html :=
  (ProofWidgets.pwHtmlToVersoHtml
    (HilbertCurve.compare_hilbert_curves 3 4 (.abs 6) (.abs 2)).toHtml
  ).addAttrs
    #[("style", "max-width: 60%; margin: 0 auto; display: block;"),
    ("alt", "A comparison of the 3rd to 4th iteration of the hilbert curve.
    Many points line up, and points that don't are not too far away.")]

def a_big_square : Verso.Output.Html :=
  Verso.Output.Html.tag "svg" #[("viewBox", "0 0 3 0.5"),
  ("alt", "It's a black square.")] (
    Verso.Output.Html.tag "rect" #[
      ("x", "1.25"),
      ("y", "0"),
      ("width", "0.5"),
      ("height", "0.5"),
      ("fill", "black")
    ] (.text false "")
  )

open Verso.Output.Html in
def displacement_plot : Verso.Output.Html := Verso.Output.Html.tag "img" #[
  ("src", "hilbertcurve/holderplot.png"),
  ("alt", "A plot of |H(t)| and 2 sqrt(t). The latter bounds |H(t)| even near 0"),
  ("style", "max-width: 50%; margin: 0 auto; display: block;")
] (.text false "")
