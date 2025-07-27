import HilbertCurveBlogPost

import VersoBlog

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " — Verso "</title>
          <link rel="stylesheet" href="/static/style.css"/>
          {{← builtinHeader }}
        </head>
        <body>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
  }
  --|>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩


def forLeanSite : Site := Site.page `ForLean (%doc HilbertCurveBlogPost.ForLean) #[]
def forTheRestSite : Site := Site.page `ForLean (%doc HilbertCurveBlogPost.ForLean) #[]

def main := blogMain theme forLeanSite
